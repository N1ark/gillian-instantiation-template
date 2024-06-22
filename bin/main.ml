open Gillian
open Instantiation

(* Typings *)
module type NameMap = Mapper.NameMap
module type IDs = MyUtils.IDs
module type FilterVals = Filter.FilterVals

type filter_mode = Filter.filter_mode

(* Indices *)
module LocationIndex = PMap.LocationIndex
module StringIndex = PMap.StringIndex

(* Transformers *)
module PMapEnt = PMap.MakeEnt
module PMap = PMap.Make
module MList = MList.Make
module Product = Product.Make
module Sum = Sum.Make
module Freeable = Freeable.Make
module Mapper = Mapper.Make
module Logger = Logger.Make
module Filter = Filter.Make
module WISLMap = WISLMap.Make

module IDs : IDs = struct
  let id1 = "left_"
  let id2 = "right_"
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

module WISLMemory =
  Mapper (WISLSubst) (PMap (LocationIndex) (Freeable (MList (Exclusive))))

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

module JSMemory =
  Filter
    (JSFilter)
    (Mapper
       (JSSubst)
       (Product
          (IDs)
          (PMap
             (LocationIndex)
             (Mapper (JSSubstInner) (PMap (StringIndex) (Exclusive))))
          (PMap (LocationIndex) (Agreement))))

(* Memory model definition *)
module MyMem = Logger (JSMemory)

(* Debug *)
module Debug = Debug.Make (MyMem)

let () = Debug.print_info ()

(* Convert custom memory model -> Gillian memory model *)
module PatchedMem = MyMonadicSMemory.Make (MyMem)

(* Gillian Instantiation *)
module SMemory = Gillian.Monadic.MonadicSMemory.Lift (PatchedMem)

(* for GIL: *)
(* module PC = ParserAndCompiler.Dummy
   module ExternalSemantics = General.External.Dummy (PC.Annot) *)

(* for JSIL: *)
module PC = Js2jsil_lib.JS2GIL_ParserAndCompiler
module ExternalSemantics = Semantics.External

module Lifter
    (Verifier : Gillian.Abstraction.Verifier.S
                  with type annot = Gil_syntax.Annot.Basic.t) =
  Gillian.Debugger.Lifter.Gil_lifter.Make (SMemory) (PC) (Verifier)

module CLI =
  Gillian.Command_line.Make (General.Init_data.Dummy) (Cmemory) (SMemory) (PC)
    (ExternalSemantics)
    (struct
      let runners = []
    end)
    (Lifter)

let () = CLI.main ()
