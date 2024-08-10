module Delayed = Gillian.Monadic.Delayed
open Utils

module StringStaticIndex : PMapIndex = struct
  let mode : index_mode = Static

  let is_valid_index = function
    | l -> Delayed.return (Some l)

  let make_fresh () = failwith "Invalid in dynamic mode"
  let default_instantiation = []
end

module IgnoreAlloc (S : MyMonadicSMemory) : MyMonadicSMemory =
  Filter
    (struct
      let mode : filter_mode = Hide
      let action_filters = [ "alloc"; "get_domainset" ]
      let preds_filters = []
    end)
    (S)

module MonadicSMemory =
  PMap (LocationIndex) (IgnoreAlloc (PMap (StringStaticIndex) (Exclusive)))

module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)
