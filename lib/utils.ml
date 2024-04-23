open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

let split_str s = match String.length s with
  | 0 -> None
  | n -> Some (String.sub s 0 1, String.sub s 1 (n - 1))

module MyInt = struct
  type t = int
  [@@deriving show, yojson]
  let compare = Stdlib.compare
end

let delayed_map (f: 'a -> 'b Delayed.t) (l: 'a list): 'b list Delayed.t =
  let rec helper l acc = match l with
    | [] -> Delayed.return acc
    | x :: xs -> Delayed.bind (f x) (fun y -> helper xs (y :: acc))
  in
  helper l []


module type IDs = sig
  val id1 : string
  val id2 : string
end

type ided =
| ID1 of string
| ID2 of string
| NotIDed of string

let str_rem_length s n = String.sub s n (String.length s - n)

module Identifier (I : IDs) = struct
  let get_ided s =
    if String.starts_with s ~prefix:I.id1
      then ID1 (str_rem_length s (String.length I.id1))
    else if String.starts_with s ~prefix:I.id2
      then ID2 (str_rem_length s (String.length I.id2))
    else NotIDed s
end
