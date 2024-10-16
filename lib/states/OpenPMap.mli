open Gil_syntax
open Gillian.Monadic

module type OpenPMapImpl = sig
  type entry
  type t [@@deriving yojson]

  val empty : t
  val fold : (Expr.t -> entry -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (entry -> bool) -> t -> bool
  val validate_index : Expr.t -> Expr.t option Delayed.t
  val get : t -> Expr.t -> (Expr.t * entry) option Delayed.t
  val set : idx:Expr.t -> idx':Expr.t -> entry -> t -> t
  val compose : t -> t -> t Delayed.t
  val substitution_in_place : Gillian.Symbolic.Subst.t -> t -> t Delayed.t
end

module type OpenPMapType = sig
  include MyMonadicSMemory.S

  type entry

  val get : t -> Expr.t -> (Expr.t * entry, err_t) result Delayed.t
  val set : idx:Expr.t -> idx':Expr.t -> entry -> t -> t
end

module MakeOfImpl
    (I_Cons : functor
      (S : MyMonadicSMemory.S)
      -> OpenPMapImpl with type entry = S.t)
    (S : MyMonadicSMemory.S) :
  OpenPMapType with type entry = S.t and type t = I_Cons(S).t

type 'e t_base_sat := 'e MyUtils.ExpMap.t
type 'e t_base_ent := 'e MyUtils.ExpMapEnt.t
type 'e t_split_sat := 'e MyUtils.ExpMap.t * 'e MyUtils.ExpMap.t
type 'e t_split_ent := 'e MyUtils.ExpMapEnt.t * 'e MyUtils.ExpMapEnt.t
type 'e t_aloc := 'e MyUtils.SMap.t

module BaseImplSat : functor (I : PMap.PMapIndex) (S : MyMonadicSMemory.S) ->
  OpenPMapImpl with type t = S.t t_base_sat and type entry = S.t

module BaseImplEnt : functor (I : PMap.PMapIndex) (S : MyMonadicSMemory.S) ->
  OpenPMapImpl with type t = S.t t_base_ent and type entry = S.t

module SplitImplSat : functor (I : PMap.PMapIndex) (S : MyMonadicSMemory.S) ->
  OpenPMapImpl with type t = S.t t_split_sat and type entry = S.t

module SplitImplEnt : functor (I : PMap.PMapIndex) (S : MyMonadicSMemory.S) ->
  OpenPMapImpl with type t = S.t t_split_ent and type entry = S.t

module ALocImpl : functor (S : MyMonadicSMemory.S) ->
  OpenPMapImpl with type t = S.t t_aloc and type entry = S.t
