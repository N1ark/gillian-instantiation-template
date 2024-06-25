open Gillian.Monadic
open Utils
open Gil_syntax

(* open Delayed.Syntax *)

(* Helpers *)
module UnsoundAlwaysOwned (S : States.MyMonadicSMemory.S) :
  States.MyMonadicSMemory.S with type t = S.t = struct
  include S

  let is_fully_owned _ = Formula.True
end

module StringIndex = struct
  include StringIndex

  let default_instantiation = [ Expr.Lit Nono ]
end

module PatchedProduct
    (IDs : IDs)
    (S1 : States.MyMonadicSMemory.S)
    (S2 : States.MyMonadicSMemory.S) :
  States.MyMonadicSMemory.S with type t = S1.t * S2.t = struct
  include Product (IDs) (S1) (S2)

  (* left side is a PMap that doesn't need any arguments, while
     the right hand side is an Agreement that requires the value.
     Split accodingly (unpatched product gives the args to both sides) *)
  let instantiate v =
    let s1, v1 = S1.instantiate [] in
    let s2, v2 = S2.instantiate v in
    ((s1, s2), v1 @ v2)
end

module MoveInToOut (S : States.MyMonadicSMemory.S) :
  States.MyMonadicSMemory.S with type t = S.t = struct
  include S

  let consume pred s ins =
    match (pred_to_str pred, ins) with
    (* the "Props" predicate considers its out an in, so it must be removed
       from consumption and then checked for equality. *)
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
      (* One of these two is wrong *)
      ("Cell", "left_points_to");
      ("Props", "left_inner_domainset");
      ("Metadata", "right_agree");
    ]
end

module JSSubstInner : NameMap = struct
  let action_substitutions = [ ("inner_get_domainset", "get_domainset") ]
  let pred_substitutions = [ ("inner_domainset", "domainset") ]
end

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

module DomainsetPatchInject : Injection with type t = BaseObject.t = struct
  type t = BaseObject.t

  let ret = Delayed.return ?learned:None ?learned_types:None
  let pre_produce _ = ret
  let pre_consume _ = ret

  let post_consume = function
    | "domainset" -> (
        function
        | (h, d), [ Expr.ESet dom ] ->
            let ensure_not_nono k =
              match States.MyUtils.ExpMap.find_opt k h with
              | Some (Some (Expr.Lit Nono)) -> false
              | _ -> true
            in
            let dom' = List.filter ensure_not_nono dom in
            ret ((h, d), [ Expr.ESet dom' ])
        | s, outs -> ret (s, outs))
    | _ -> ret

  let pre_execute_action _ = ret
  let post_execute_action _ = ret
end

module Object =
  Mapper
    (JSSubstInner)
    (MoveInToOut (Injector (DomainsetPatchInject) (BaseObject)))

(* Note JS doesn't actually have a freed, but rather just erases the field.
   In practice the field doesn't get accessed anyways so it not existing or being
   Freed should behave the same. A post-action injection could be used to replace
   Freed with None for better fidelity. *)
module BaseMemory =
  PMap
    (LocationIndex)
    (Freeable (UnsoundAlwaysOwned (PatchedProduct (IDs) (Object) (Agreement))))

module JSInjection : Injection with type t = BaseMemory.t = struct
  type t = BaseMemory.t

  let ret = Delayed.return ?learned:None ?learned_types:None
  let pre_produce _ = ret
  let pre_consume _ = ret
  let post_consume _ = ret

  let pre_execute_action = function
    | "Alloc" -> (
        function
        (* Allocations are given two parameters, [empty; ###], we can ignore
           the empty and pass the second value wich is the metadata location *)
        | s, Expr.Lit Empty :: args | s, args -> ret (s, args))
    | _ -> ret

  let post_execute_action _ = ret
end

(* Actual exports *)

module ParserAndCompiler = Js2jsil_lib.JS2GIL_ParserAndCompiler
module ExternalSemantics = Semantics.External

module MonadicSMemory =
  Filter (JSFilter) (Injector (JSInjection) (Mapper (JSSubst) (BaseMemory)))
