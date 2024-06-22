open Gillian.Monadic
open Utils

(* Helpers *)
module JSSubst : NameMap = struct
  let action_substitutions =
    [
      ("GetCell", "left_load");
      ("SetCell", "left_store");
      ("Alloc", "left_alloc");
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

module BaseMemory =
  Product
    (IDs)
    (PMap
       (LocationIndex)
       (Mapper (JSSubstInner) (PMap (StringIndex) (Exclusive))))
    (PMap (LocationIndex) (Agreement))

module MonadicSMemory = Filter (JSFilter) (Mapper (JSSubst) (BaseMemory))
