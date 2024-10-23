open States

(* Typings *)
module type ActionAddition = ActionAdder.ActionAddition
module type FilterVals = Filter.FilterVals
module type IDs = MyUtils.IDs
module type Injection = Injector.Injection
module type NameMap = Mapper.NameMap
module type MyMonadicSMemory = MyMonadicSMemory.S
module type PMapIndex = OpenPMap.PMapIndex

type filter_mode = Filter.filter_mode
type index_mode = OpenPMap.index_mode

(* Helpers *)
module DummyInject = Injector.DummyInject

module IDs : IDs = struct
  let id1 = "left_"
  let id2 = "right_"
end

(* Indices *)
module LocationIndex = OpenPMap.LocationIndex
module IntegerIndex = OpenPMap.IntegerIndex
module StringIndex = OpenPMap.StringIndex

(* Leaves *)
module Agreement = Agreement
module Exclusive = Exclusive
module Fractional = Fractional

(* Transformers *)
module ActionAdder = ActionAdder.Make
module Filter = Filter.Make
module Freeable = Freeable.Make
module Injector = Injector.Make
module Logger = Logger.Make
module Mapper = Mapper.Make
module MList = MList.Make
module Product = Product.Make
module Sum = Sum.Make

(* PMaps *)
module ALocPMap = OpenPMap.MakeOfImpl (OpenPMap.ALocImpl)
module PMap (I : PMapIndex) = OpenPMap.MakeOfImpl (OpenPMap.BaseImplSat (I))

module SplitPMap (I : PMapIndex) = OpenPMap.MakeOfImpl (OpenPMap.SplitImplSat (I))

module OpenALocPMap = OpenPMap.MakeOpenOfImpl (OpenPMap.ALocImpl)

module OpenSplitPMap (I : PMapIndex) =
  OpenPMap.MakeOpenOfImpl (OpenPMap.SplitImplSat (I))

module OpenPMap (I : PMapIndex) =
  OpenPMap.MakeOpenOfImpl (OpenPMap.BaseImplSat (I))
