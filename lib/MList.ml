open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

module DR = Delayed_result

open Utils

module EMap = Prelude.Map.Make (Expr)

let expr_is_int e = match e with
  | Expr.Lit (Literal.Int _) -> true
  | _ -> false

let expr_to_int e = match e with
  | Expr.Lit (Literal.Int i) -> Z.to_int i
  | _ -> failwith "Expected integer expression"

module Make
  (S: MyMonadicSMemory.S) : MyMonadicSMemory.S = struct

    type t = (S.t EMap.t) * (Expr.t option)
    [@@deriving yojson]

    let pp fmt ((b, n): t) =
      let pp_binding fmt (k, v) = Format.fprintf fmt "%a -> %a" Expr.pp k S.pp v in
      let pp_opt fmt = function
        | Some n -> Format.fprintf fmt "Some %a" Expr.pp n
        | None -> Format.fprintf fmt "None" in
      Format.fprintf fmt "{ %a }, %a" (Format.pp_print_list pp_binding) (EMap.bindings b) pp_opt n


    let show s = Format.asprintf "%a" pp s

    type c_fix_t = | SubFix of Expr.t * S.c_fix_t
    [@@deriving show]

    type err_t =
    | OutOfBounds of Expr.t * Expr.t (* Accessed index, list length *)
    | MissingCell of Expr.t (* Accessed index *)
    | MissingLength
    | SubError of Expr.t * S.err_t
    [@@deriving show, yojson]

    type action = | SubAction of S.action

    let action_from_str str = Option.map (fun a -> SubAction a) (S.action_from_str str)

    type pred =
    | Length
    | SubPred of S.pred
    let pred_from_str = function
    | "length" -> Some Length
    | str -> Option.map (fun p -> SubPred p) (S.pred_from_str str)
    let pred_to_str = function
      | Length -> "length"
      | SubPred p -> S.pred_to_str p

    let init (): t = (EMap.empty, None)
    let clear s = s (* TODO *)

    (* Returns the (reduced) key and value in the map if present *)
    let state_at ((b, n): t) idx =
      let open DR.Syntax in
      let open Delayed.Syntax in
      let* idx = Delayed.reduce idx in
      let** () = match n with
      | Some n ->
        if%sat Formula.Infix.(idx #>= n)
        then DR.error (OutOfBounds (idx, n))
        else DR.ok ()
      | _ -> DR.ok () in
      match EMap.find_opt idx b with
      | Some v -> DR.ok (idx, v) (* Direct match *)
      | None ->
        let rec find_match = function
          | [] -> DR.error (MissingCell idx)
          | (k, v) :: tl ->
            if%sat Formula.Infix.(k #== idx)
              (* TODO: reduce k, and replace it in the map.
                 This means instead of returning idx * val, we'd return
                 t * idx * val, with t the updated map containing the reduced idx.
                 I'm not super sure it's needed though, since an index is always
                 initially reduce before being inserted. *)
            then DR.ok (k, v)
            else find_match tl in
        find_match (EMap.bindings b)

    let execute_action action ((b, n): t) (args: Values.t list): (t * Values.t list, err_t) DR.t =
      let open DR.Syntax in
      let open Delayed.Syntax in
      match action, args with
      | SubAction a, idx :: args ->
        let** (idx, s) = state_at (b, n) idx in
        let+ r = S.execute_action a s args in (match r with
        | Ok (s', v) -> Ok ((EMap.add idx s' b, n), v)
        | Error e -> Error (SubError (idx, e))
        )
      | SubAction _, [] -> failwith "Missing index for sub-action"

    let consume pred (b, n) ins =
      let open DR.Syntax in
      let open Delayed.Syntax in
      match pred, ins with
      | SubPred p, idx :: ins ->
        let** (idx, s) = state_at (b, n) idx in
        let+ r = S.consume p s ins in (match r with
        | Ok (s', outs) -> Ok ((EMap.remove idx b, n), outs)
        | Error e -> Error (SubError (idx, e))
        )
      | SubPred _, [] -> failwith "Missing index for sub-predicate consume"
      | Length, [] -> (
        match n with
        | Some n -> DR.ok ((b, None), [n])
        | None -> DR.error MissingLength
      )
      | Length, _ -> failwith "Invalid arguments for length consume"

    let produce pred (b, n) args =
      let open Delayed.Syntax in
      match pred, args with
      | SubPred p, idx :: args -> (
        let* r = state_at (b, n) idx in (match r with
        | Ok (idx, s) ->
          let+ s' = S.produce p s args in
          (EMap.add idx s' b, n)
        | Error e -> match e with
          | MissingCell _ -> (
            let s = S.init () in
            let+ s' = S.produce p s args in
            (EMap.add idx s' b, n))
          | _ -> Delayed.vanish ()))
      | SubPred _, [] -> failwith "Missing index for sub-predicate produce"
      | Length, [n'] -> (
        match n with
        | Some _ ->
          Logging.normal (fun m -> m "Warning MList: vanishing due to duplicate length";);
          Delayed.vanish ()
        | None -> Delayed.return (b, Some n'))
      | Length, _ -> failwith "Invalid arguments for length produce"

    let compose s1 s2 = failwith "Not implemented"

    let is_fully_owned s = failwith "Implement here (is_fully_owned)"

    let substitution_in_place sub (b, n) =
      let open Delayed.Syntax in
      let mapper (idx, s) =
        let+ s' = S.substitution_in_place sub s in
        let idx' = Subst.subst_in_expr sub idx ~partial:true in (idx', s') in
      let map_entries = EMap.bindings b in
      let+ sub_entries = Delayed.all (List.map mapper map_entries) in
      let merge v opt = match opt with (* if entry exists, merge the values *)
        | None -> Some v
        | Some v' -> Some (S.compose v v') in
      let b' = List.fold_left (fun acc (idx, s) -> EMap.update idx (merge s) acc) EMap.empty sub_entries in
      let n' = Option.map (Subst.subst_in_expr sub ~partial:true) n in
      (b', n')

    let lvars (b, n) =
      let open Containers.SS in
      let lvars_map = EMap.fold (fun k v acc -> union (union (Expr.lvars k) (S.lvars v)) acc) b empty in
      match n with
      | Some n -> union lvars_map (Expr.lvars n)
      | None -> lvars_map

    let alocs (b, n) =
      let open Containers.SS in
      let alocs_map = EMap.fold (fun k v acc -> union (union (Expr.alocs k) (S.alocs v)) acc) b empty in
      match n with
      | Some n -> union alocs_map (Expr.alocs n)
      | None -> alocs_map

    let assertions (b, n) =
      let mapper = fun k (p, i, o) -> (SubPred p, k :: i, o) in
      EMap.fold (fun k v acc -> acc @ List.map (mapper k) (S.assertions v)) b []

    let get_recovery_tactic (b, n) = function
    | SubError (idx, e) -> (
      match EMap.find_opt idx b with
      | Some s -> S.get_recovery_tactic s e
      | None -> failwith "Invalid index in get_recovery_tactic"
    )
    | _ -> Gillian.General.Recovery_tactic.none

    let get_fixes (b, n) pfs tenv = function
    | SubError (idx, e) -> (
      let v = EMap.find idx b in
      let mapper = fun (fs, fml, t, c) -> (List.map (fun f -> SubFix (idx, f)) fs, fml, t, c) in
      List.map mapper (S.get_fixes v pfs tenv e)
    )
    | _ -> failwith "Invalid error in get_fixes"

    let can_fix = function
    | SubError (_, e) -> S.can_fix e
    | MissingCell _ -> false
    | OutOfBounds _ -> false
    | MissingLength -> false


    let apply_fix (b, n) = function
    | SubFix (idx, f) ->
      let open Delayed.Syntax in
      let s = EMap.find idx b in
      let+ r = S.apply_fix s f in
      match r with
      | Ok s' -> Ok (EMap.add idx s' b, n)
      | Error e -> Error (SubError (idx, e))
end
