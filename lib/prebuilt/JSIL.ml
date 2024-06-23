open Gillian.Monadic
open Gil_syntax
open Utils
open Delayed.Syntax

(* Helpers *)
module JSSubst : NameMap = struct
  let action_substitutions =
    [
      ("GetCell", "left_load");
      ("SetCell", "left_store");
      ("Alloc", "right_alloc");
      ("GetMetadata", "right_load");
    ]

  let pred_substitutions =
    [
      (* One of these two is wrong *)
      ("Cell", "left_points_to");
      ("Props", "left_innerdomainset");
      ("Metadata", "right_agree");
    ]
end

module JSSubstInner : NameMap = struct
  let action_substitutions = []
  let pred_substitutions = [ ("innerdomainset", "domainset") ]
end

module JSFilter : FilterVals = struct
  let mode : filter_mode = ShowOnly
  let action_filters = [ "GetCell"; "SetCell"; "Alloc"; "GetMetadata" ]
  let preds_filters = [ "Cell"; "Props"; "Metadata" ]
end

(* Actual exports *)

module ParserAndCompiler = Js2jsil_lib.JS2GIL_ParserAndCompiler
module ExternalSemantics = Semantics.External

module ProdL =
  PMap (LocationIndex) (Mapper (JSSubstInner) (PMap (StringIndex) (Exclusive)))

module ProdR = PMap (LocationIndex) (Agreement)
module BaseMemory = Product (IDs) (ProdL) (ProdR)

module JSInjection : Injection with type t = BaseMemory.t = struct
  type t = BaseMemory.t

  let ret = Delayed.return ?learned:None ?learned_types:None
  let pre_produce _ = ret
  let pre_consume _ = ret
  let post_consume _ = ret

  let pre_execute_action action =
    match action with
    | "Alloc" -> (
        function
        (* Allocations are given two parameters, [empty; ###], we can ignore
           the empty and pass the second value wich is the metadata location *)
        | s, Expr.Lit Empty :: args | s, args -> ret (s, args))
    | _ -> ret

  let post_execute_action action ((l, r), rets) =
    match (action, rets) with
    | "Alloc", [ loc ] -> (
        (* After allocating on the right side, allocate on the address map as well *)
        let action = Option.get (ProdL.action_from_str "alloc") in
        let* res = ProdL.execute_action action l [] in
        match res with
        (* Ensuring the allocated address is the same as for the metadata! *)
        | Ok (l', [ loc' ]) ->
            Delayed.return
              ~learned:[ Formula.Infix.(loc #== loc') ]
              ((l', r), rets)
        | Ok (l', _) -> ret ((l', r), rets)
        (* Shouldn't happen – don't have better way of handling atm *)
        | _ ->
            Format.printf
              "Error in post_execute_action Alloc: generated %a, is ok? %b"
              Expr.pp loc (Result.is_ok res);
            Delayed.vanish ())
    | _, _ -> ret ((l, r), rets)
end

module MonadicSMemory =
  Filter (JSFilter) (Injector (JSInjection) (Mapper (JSSubst) (BaseMemory)))
