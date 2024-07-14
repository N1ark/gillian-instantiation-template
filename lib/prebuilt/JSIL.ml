open Gillian.Monadic
open Utils
open Gil_syntax
module ExpMap = States.MyUtils.ExpMap

(* open Delayed.Syntax *)

(* Allow freeable to always free (since it's ok in JS) *)
module UnsoundAlwaysOwned (S : States.MyMonadicSMemory.S) :
  States.MyMonadicSMemory.S with type t = S.t = struct
  include S

  let is_fully_owned _ _ = Formula.True
end

(* Default instantiation is Nono *)
module StringIndex = struct
  include StringIndex

  let default_instantiation = [ Expr.Lit Nono ]
end

(* left side is a PMap that doesn't need any arguments, while
   the right hand side is an Agreement that requires the value.
   Split accordingly (unpatched product gives the args to both sides) *)
module PatchedProduct
    (IDs : IDs)
    (S1 : States.MyMonadicSMemory.S)
    (S2 : States.MyMonadicSMemory.S) :
  States.MyMonadicSMemory.S with type t = S1.t * S2.t = struct
  include Product (IDs) (S1) (S2)

  let instantiate v =
    let s1, v1 = S1.instantiate [] in
    let s2, v2 = S2.instantiate v in
    ((s1, s2), v1 @ v2)
end

(* the "Props" predicate considers its out an in, so it must be removed
   from consumption and then checked for equality. *)
module MoveInToOut (S : States.MyMonadicSMemory.S) :
  States.MyMonadicSMemory.S with type t = S.t = struct
  include S

  let consume pred s ins =
    match (pred_to_str pred, ins) with
    | "domainset", [ out ] -> (
        let open Delayed_result.Syntax in
        let** s', outs = S.consume pred s [] in
        match outs with
        | [ out' ] ->
            if%ent Formula.Infix.(out #== out') then Delayed_result.ok (s', [])
            else
              failwith
                (Fmt.str
                   "Mismatch in domainset (Props) consumption - got: %a, \
                    expected %a"
                   Expr.pp out' Expr.pp out)
        | _ -> Delayed_result.ok (s', outs))
    | _ -> consume pred s ins
end

(* Outer substitutions for JS *)
module JSSubst : NameMap = struct
  let action_substitutions =
    [
      ("GetCell", "left_load");
      ("SetCell", "left_store");
      ("GetAllProps", "left_inner_get_domainset");
      ("Alloc", "alloc");
      ("DeleteObject", "free");
      ("GetMetadata", "right_load");
    ]

  let pred_substitutions =
    [
      ("Cell", "left_points_to");
      ("Props", "left_inner_domainset");
      ("Metadata", "right_agree");
    ]
end

(* Substitutions for internal PMap (avoids name clash) *)
module JSSubstInner : NameMap = struct
  let action_substitutions = [ ("inner_get_domainset", "get_domainset") ]
  let pred_substitutions = [ ("inner_domainset", "domainset") ]
end

(* Outer pred/action filter *)
module JSFilter : FilterVals = struct
  let mode : filter_mode = ShowOnly

  let action_filters =
    [
      "GetCell";
      "test";
      "SetCell";
      "Alloc";
      "DeleteObject";
      "GetMetadata";
      "GetAllProps";
    ]

  let preds_filters = [ "Cell"; "Props"; "Metadata" ]
end

module BaseObject = PMap (StringIndex) (Exclusive)

(* - Ignore "Nono" values in the domainset
   - Similarly to WISL, actions on the PMap return the index used *)
module DomainsetPatchInject : Injection with type t = BaseObject.t = struct
  include DummyInject (BaseObject)

  let post_execute_action _ (s, args, rets) =
    let rets' =
      match (args, rets) with
      | _, ([] as rets) | [], rets -> rets
      | idx :: _, rets -> idx :: rets
    in
    Delayed.return (s, args, rets')

  let post_consume p ((h, d), outs) =
    match (p, outs) with
    | "domainset", [ Expr.ESet dom ] ->
        let ensure_not_nono k =
          match States.MyUtils.ExpMap.find_opt k h with
          | Some (Some (Expr.Lit Nono)) -> false
          | _ -> true
        in
        let dom' = List.filter ensure_not_nono dom in
        Delayed.return ((h, d), [ Expr.ESet dom' ])
    | _ -> Delayed.return ((h, d), outs)
end

module Object =
  Mapper
    (JSSubstInner)
    (MoveInToOut (Injector (DomainsetPatchInject) (BaseObject)))

(* Note JS doesn't actually have a freed, but rather just erases the field.
   In practice the field doesn't get accessed anyways so it not existing or being
   Freed should behave the same. A post-action injection could be used to replace
   Freed with None for better fidelity. *)
module BaseMemoryContent =
  Freeable (UnsoundAlwaysOwned (PatchedProduct (IDs) (Object) (Agreement)))

(* When allocating, two params are given:
    - the address to allocate into (can be 'empty' to generate new address) - defaults to empty
    - the metadata address, which is the value of the agreement (rhs of the object product) - defaults to null
   Need to take that into consideration + similarly to WISL, return the index on each action. *)
module MemoryPatchedAlloc = struct
  include ALocPMap (BaseMemoryContent)
  module SS = Gillian.Utils.Containers.SS
  module SMap = States.ALocPMap.SMap

  (* Patch the alloc action *)
  let execute_action a (h, d) args =
    let open Delayed_result.Syntax in
    match (a, args) with
    | Alloc, [ idx; v ] ->
        let** idx =
          match idx with
          | Expr.Lit Empty -> Delayed_result.ok (ALoc.alloc ())
          | _ -> get_loc idx
        in
        Logging.tmi (fun f ->
            f "Allocating -> %s, args (%a)" idx
              (Fmt.list ~sep:Fmt.comma Expr.pp)
              args);
        let s, v = BaseMemoryContent.instantiate [ v ] in
        let h' = SMap.add idx s h in
        let d' = modify_domain (SS.add idx) d in
        Delayed_result.ok ((h', d'), Expr.loc_from_loc_name idx :: v)
    | _, idx :: _ ->
        let** s', rets = execute_action a (h, d) args in
        Delayed_result.ok (s', idx :: rets)
    | _ -> execute_action a (h, d) args
end

(* Actual exports *)

module ParserAndCompiler = Js2jsil_lib.JS2GIL_ParserAndCompiler
module ExternalSemantics = Semantics.External

module MonadicSMemory =
  Filter (JSFilter) (Mapper (JSSubst) (MemoryPatchedAlloc))
