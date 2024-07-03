open Utils
module Delayed = Gillian.Monadic.Delayed
module BaseMemory = PMap (LocationIndex) (Freeable (MList (Exclusive)))

module MapIndexRetInjection : Injection with type t = BaseMemory.t = struct
  include DummyInject (BaseMemory)

  let post_execute_action _ (s, args, rets) =
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
