open Utils
open Gil_syntax
module Delayed = Gillian.Monadic.Delayed

(* Make the default value null *)
module ExclusiveNull = struct
  include Exclusive

  let instantiate = function
    | [] -> (Some (Expr.Lit Null), [])
    | [ v ] -> (Some v, [])
    | _ -> failwith "ExclusiveNull: instantiate: too many arguments"
end

module MemoryChunk = MList (ExclusiveNull)

module ListIndexRetInjection : Injection with type t = MemoryChunk.t = struct
  include DummyInject (MemoryChunk)

  let post_execute_action _ (s, args, rets) =
    let rets' =
      match (args, rets) with
      | _, ([] as rets) | [], rets -> rets
      | idx :: _, rets -> idx :: rets
    in
    Delayed.return (s, args, rets')

  (* Requires returning first index in list on instantiation (0) *)
  let post_instantiate (s, rets) = (s, Expr.zero_i :: rets)
end

module BaseMemory =
  PMap
    (LocationIndex)
    (Freeable (Injector (ListIndexRetInjection) (MemoryChunk)))

module MapIndexRetInjection : Injection with type t = BaseMemory.t = struct
  include DummyInject (BaseMemory)

  let post_execute_action a (s, args, rets) =
    match a with
    | "alloc" -> Delayed.return (s, args, rets)
    | _ ->
        let rets' =
          match (args, rets) with
          | _, ([] as rets) | [], rets -> rets
          | idx :: _, rets -> idx :: rets
        in
        Delayed.return (s, args, rets')
end

module WISLSubst : NameMap = struct
  let action_substitutions =
    [
      ("alloc", "alloc");
      ("dispose", "free");
      ("setcell", "store");
      ("getcell", "load");
    ]

  let pred_substitutions =
    [ ("cell", "points_to"); ("freed", "freed"); ("bound", "length") ]
end

(* Actual Exports *)

module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module MonadicSMemory =
  Mapper (WISLSubst) (Injector (MapIndexRetInjection) (BaseMemory))
