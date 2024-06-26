(*
This is not valid syntax. Just ideation of what declaring state model and state model
transformers could look like with nice PPX integration and the already existing monads.
*)

module type Value = sig
  type t
end

module Exc (V : Value) = struct
  type t = V.t option
  type err = NotOwned | DoubleFree
  type miss = unit

  let load s =
    match s with
    | Some x -> ok (s, [ x ])
    | None -> miss ()
  [@@action]
  (* %-- generates an action, taking name of the function *)

  let store s v =
    (* number of args inferred *)
    match s with
    | Some x -> ok (Some v, [])
    | None -> miss ()
  [@@action]

  let points_to s =
    match s with
    | Some x -> ok (None, [ x ])
    | None -> miss ()
  [@@consumer]
  (* %-- generates a predicate, taking name of the function *)

  let points_to s v =
    match s with
    | Some x -> vanish ()
    | None -> return (Some v)
  [@@producer]
  (* ^-- must be matched with a consumer! *)
end
[@@state_model]

module Freeable (S : StateModel) = struct
  include S

  type t = Val of S.t | Freed | None
  type err = NotOwned | DoubleFree | IncompatibleState [@@inherit]
  (* inherit adds a "Sub _" <---------------------------^^^^^^^^^ *)

  type miss = MissFreed | MissState [@@inherit]

  let free s =
    match s with
    | Val x when S.is_exc_owned x -> ok (Freed, [])
    | Val x -> error NotOwned
    | Freed -> error DoubleFree
    | None -> miss MissState
  [@@action]

  let freed s =
    match s with
    | Val x -> lfail IncompatibleState
    | Freed -> ok (None, [])
    | None -> miss MissFreed
  [@@consumer]

  let freed s =
    match s with
    | Val x -> vanish ()
    | Freed -> vanish ()
    | None -> return Freed
  [@@producer]
end
[@@state_model]
