open Gillian.Utils
open Gillian.Monadic
open Gil_syntax

module type IDs = sig
  val id1 : string
  val id2 : string
end

type ided = ID1 of string | ID2 of string | NotIDed of string

let str_rem_length s n = String.sub s n (String.length s - n)

module Identifier (I : IDs) = struct
  let get_ided s =
    if String.starts_with s ~prefix:I.id1 then
      ID1 (str_rem_length s (String.length I.id1))
    else if String.starts_with s ~prefix:I.id2 then
      ID2 (str_rem_length s (String.length I.id2))
    else NotIDed s
end

let pp_bindings ~pp_k ~pp_v iter fmt m =
  let pp_binding fmt (k, v) = Fmt.pf fmt "%a -> %a" pp_k k pp_v v in
  Fmt.pf fmt "@[<v>%a@]"
    ( Fmt.iter_bindings ~sep:(Fmt.any "@\n@\n") iter @@ fun ft b ->
      pp_binding ft b )
    m

module type SymExprMap = sig
  include Prelude.Map.S with type key = Expr.t

  val sym_find_opt : key -> 'a t -> ('a t * key * 'a) option Delayed.t

  val sym_find_default :
    key -> 'a t -> default:(unit -> 'a) -> ('a t * key * 'a) Delayed.t

  val sym_find_res :
    key -> 'a t -> err:'b -> ('a t * key * 'a, 'b) result Delayed.t

  val sym_compose :
    ('a -> 'a -> 'a Delayed.t) -> (Expr.t * 'a) list -> 'a t -> 'a t Delayed.t

  val sym_merge : ('a -> 'a -> 'a Delayed.t) -> 'a t -> 'a t -> 'a t Delayed.t

  val make_pp :
    (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module ExpMap : SymExprMap = struct
  module Temp = Prelude.Map.Make (Expr)
  include Temp

  let sym_find_opt k m =
    (* TODO: commented code doesn't seem to give any improvement. (slows down????) *)
    (* let open Delayed.Syntax in *)
    match Temp.find_opt k m with
    | Some v -> Delayed.return (Some (m, k, v)) (* Direct match *)
    | None ->
        let rec find_match = function
          | _, [] -> Delayed.return None
          | m, (k', v) :: tl ->
              (* let* k' = Delayed.reduce k' in *)
              if%sat Formula.Infix.(k' #== k) then
                (* let m' = Temp.add k' v (Temp.remove k m) in *)
                Delayed.return (Some (m, k', v))
              else find_match (m, tl)
        in
        find_match (m, bindings m)

  let sym_find_default k m ~default =
    let open Delayed.Syntax in
    let* res = sym_find_opt k m in
    match res with
    | Some (m, k, v) -> Delayed.return (m, k, v)
    | None -> Delayed.return (m, k, default ())

  let sym_find_res k m ~err =
    let open Delayed.Syntax in
    let+ res = sym_find_opt k m in
    match res with
    | Some (m, k, v) -> Ok (m, k, v)
    | None -> Error err

  (** Symbolically composes a map with a list of entries, composing entries when they
    are found to match. *)
  let sym_compose
      (compose : 'a -> 'a -> 'a Delayed.t)
      (l : (Expr.t * 'a) list)
      (m : 'a t) : 'a t Delayed.t =
    let open Delayed.Syntax in
    let compose_binding m (k, v) =
      let* m = m in
      let* r = sym_find_opt k m in
      match r with
      | Some (m', k', v') ->
          let+ v'' = compose v v' in
          add k' v'' m'
      | None -> Delayed.return (add k v m)
    in
    List.fold_left compose_binding (Delayed.return m) l

  let sym_merge compose m1 m2 = sym_compose compose (bindings m2) m1
  let make_pp pp_v = pp_bindings ~pp_k:Expr.pp ~pp_v iter
end

(**
  Same as [ExpMap] but with the [sym_find_opt] function using entailement instead of
  satifiability.
*)
module ExpMapEnt : SymExprMap = struct
  include ExpMap

  let sym_find_opt k m =
    (* TODO: commented code doesn't seem to give any improvement. (slows down????) *)
    (* let open Delayed.Syntax in *)
    match find_opt k m with
    | Some v -> Delayed.return (Some (m, k, v)) (* Direct match *)
    | None ->
        let rec find_match = function
          | _, [] -> Delayed.return None
          | m, (k', v) :: tl ->
              (* let* k' = Delayed.reduce k' in *)
              if%ent Formula.Infix.(k' #== k) then
                (* let m' = Temp.add k' v (Temp.remove k m) in *)
                Delayed.return (Some (m, k', v))
              else find_match (m, tl)
        in
        find_match (m, bindings m)
end

let pp_opt pp_v fmt = function
  | Some v -> Format.fprintf fmt "Some %a" pp_v v
  | None -> Format.pp_print_string fmt "None"

let bind_vanish_on_err (x : ('a, 'e) result Delayed.t) (f : 'a -> 'b Delayed.t)
    : 'b Delayed.t =
  let open Delayed.Syntax in
  let* x = x in
  match x with
  | Ok x -> f x
  | Error _ -> Delayed.vanish ()

let ( let*? ) = bind_vanish_on_err
