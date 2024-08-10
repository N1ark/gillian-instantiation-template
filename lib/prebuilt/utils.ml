open States

(* Typings *)
module type ActionAddition = ActionAdder.ActionAddition
module type FilterVals = Filter.FilterVals
module type IDs = MyUtils.IDs
module type Injection = Injector.Injection
module type NameMap = Mapper.NameMap
module type MyMonadicSMemory = MyMonadicSMemory.S
module type PMapIndex = PMap.PMapIndex

type filter_mode = Filter.filter_mode
type index_mode = PMap.index_mode

(* Helpers *)
module DummyInject = Injector.DummyInject

module IDs : IDs = struct
  let id1 = "left_"
  let id2 = "right_"
end

(* Indices *)
module LocationIndex = PMap.LocationIndex
module StringIndex = PMap.StringIndex

(* Leaves *)
module Agreement = Agreement
module Exclusive = Exclusive
module Fractional = Fractional

(* Transformers *)
module ActionAdder = ActionAdder.Make
module ALocPMap = ALocPMap.Make
module Filter = Filter.Make
module Freeable = Freeable.Make
module Injector = Injector.Make
module Logger = Logger.Make
module Mapper = Mapper.Make
module MList = MList.Make
module PMap = States.PMap.Make
module PMapEnt = States.PMap.MakeEnt
module Product = Product.Make
module SplitPMap = SplitPMap.Make
module Sum = Sum.Make
