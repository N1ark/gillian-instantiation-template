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

  let pp ft (s1, s2) = Fmt.pf ft "%a with metadata %a" S1.pp s1 S2.pp s2
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

module BaseObject = struct
  include PMap (StringIndex) (Exclusive)

  let pp ft ((h, d) : t) =
    let d =
      match d with
      | Some (Expr.ESet l) -> Some (Expr.ESet (List.sort Expr.compare l))
      | e -> e
    in
    let open Fmt in
    let pp_bindings =
      iter_bindings ~sep:comma ExpMap.iter
        (hbox (parens (pair ~sep:(any " :") Expr.pp Exclusive.pp)))
    in
    pf ft "[ @[%a@] | @[%a@] ]" pp_bindings h (option Expr.pp) d
end

(* - Ignore "Nono" values in the domainset *)
module DomainsetPatchInject : Injection with type t = BaseObject.t = struct
  include DummyInject (BaseObject)

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
module ALoc_MemoryPatchedAlloc = struct
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
    | _ -> execute_action a (h, d) args

  let pp ft ((h, _) : t) =
    let open Fmt in
    let sorted_locs_with_vals =
      SMap.bindings h |> List.sort (fun (k1, _) (k2, _) -> String.compare k1 k2)
    in
    let pp_one ft (loc, fv_pairs) =
      pf ft "@[%s |-> %a@]" loc BaseMemoryContent.pp fv_pairs
    in
    (list ~sep:(any "@\n") pp_one) ft sorted_locs_with_vals
end

module Base_MemoryPatchedAlloc = struct
  include PMap (LocationIndex) (BaseMemoryContent)
  module SS = Gillian.Utils.Containers.SS

  (* Patch the alloc action *)
  let execute_action a (h, d) args =
    match (a, args) with
    | Alloc, [ idx; v ] ->
        let idx =
          match idx with
          | Expr.Lit Empty -> LocationIndex.make_fresh ()
          | _ -> idx
        in
        Logging.tmi (fun f ->
            f "Allocating -> %a, args (%a)" Expr.pp idx
              (Fmt.list ~sep:Fmt.comma Expr.pp)
              args);
        let s, v = BaseMemoryContent.instantiate [ v ] in
        let h' = ExpMap.add idx s h in
        let d' = modify_domain (fun d -> idx :: d) d in
        Delayed_result.ok ((h', d'), idx :: v)
    | _ -> execute_action a (h, d) args

  let pp ft ((h, _) : t) =
    let open Fmt in
    let sorted_locs_with_vals =
      ExpMap.bindings h |> List.sort (fun (k1, _) (k2, _) -> Expr.compare k1 k2)
    in
    let pp_one ft (loc, fv_pairs) =
      pf ft "@[%a |-> %a@]" Expr.pp loc BaseMemoryContent.pp fv_pairs
    in
    (list ~sep:(any "@\n") pp_one) ft sorted_locs_with_vals
end

(* Actual exports *)

module ParserAndCompiler = Js2jsil_lib.JS2GIL_ParserAndCompiler
module ExternalSemantics = Semantics.External

module Base_MonadicSMemory =
  Filter (JSFilter) (Mapper (JSSubst) (Base_MemoryPatchedAlloc))

module ALoc_MonadicSMemory =
  Filter (JSFilter) (Mapper (JSSubst) (ALoc_MemoryPatchedAlloc))
