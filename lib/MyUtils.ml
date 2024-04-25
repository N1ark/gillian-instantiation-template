open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

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

module ExpMap = struct
  module Temp = Prelude.Map.Make (Expr)
  include Temp

  let sym_find_opt k m =
    match Temp.find_opt k m with
    | Some v -> Delayed.return (Some (k, v)) (* Direct match *)
    | None ->
      let rec find_match = function
        | [] -> Delayed.return None
        | (k', v) :: tl ->
          if%sat Formula.Infix.(k' #== k)
            (* TODO: reduce k, and replace it in the map.
               This means instead of returning idx * val, we'd return
               t * idx * val, with t the updated map containing the reduced idx.
               I'm not super sure it's needed though, since an index is always
               initially reduce before being inserted. *)
          then Delayed.return (Some (k', v))
          else find_match tl in
      find_match (bindings m)

  let sym_find_default k m ~default =
    let open Delayed.Syntax in
    let* res = sym_find_opt k m in
    match res with
    | Some (k, v) -> Delayed.return (k, v)
    | None -> Delayed.return (k, default ())

  let sym_find_res k m ~err =
    let open Delayed.Syntax in
    let+ res = sym_find_opt k m in
    match res with
    | Some (k, v) -> Ok (k, v)
    | None -> Error err

  let make_pp pp_v =
    fun fmt m ->
      let pp_binding fmt (k, v) =
        Format.fprintf fmt "%a -> %a" Expr.pp k pp_v v in
      Format.fprintf fmt
        "@[<hov 2>{%a}@]"
        (Format.pp_print_list pp_binding)
        (bindings m)

end

let pp_opt pp_v fmt = function
  | Some v -> Format.fprintf fmt "Some %a" pp_v v
  | None -> Format.pp_print_string fmt "None"

let bind_vanish_on_err (x : ('a, 'e) result Delayed.t) (f : 'a Delayed.t -> 'b Delayed.t) : 'b Delayed.t =
  let open Delayed.Syntax in
  let* x = x in
  match x with
  | Ok x -> f (Delayed.return x)
  | Error _ -> Delayed.vanish ()

let ( let*? ) = bind_vanish_on_err
