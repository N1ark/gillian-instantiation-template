open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

open MyUtils

(** Type for the domain of a PMap.
    Allows configuring it to either have static or dynamic indexing:
    - Static: indexes are created by the memory model on allocation
    - Dynamic: indexes are given by the user on allocation
    The user must provide the index on allocation in dynamic mode, and mustn't provide it in static mode.
    is_valid_index must always be implemented, while make_fresh is only needed in static mode.
     *)
module type PMapIndex = sig
  val mode : [`Static | `Dynamic]
  val is_valid_index : Expr.t -> bool Delayed.t
  val make_fresh : unit -> Expr.t Delayed.t
end

module LocationIndex : PMapIndex = struct
  let mode = `Static
  let is_valid_index = function
  | Expr.ALoc _ | Expr.Lit (Loc _) -> Delayed.return true
  | _ -> Delayed.return false
  let make_fresh () =
    let loc_name = ALoc.alloc () in
    Delayed.return (Expr.ALoc loc_name)
end

module StringIndex : PMapIndex = struct
  let mode = `Dynamic
  let is_valid_index = function
  | Expr.Lit (String _) -> Delayed.return true
  | _ -> Delayed.return false
  let make_fresh () = failwith "Not implemented (StringIndex.make_fresh)"
end

module Make
  (I: PMapIndex)
  (S: MyMonadicSMemory.S) : MyMonadicSMemory.S = struct

  type t = (S.t ExpMap.t) * (Expr.t option)
  [@@deriving yojson]

  let pp fmt ((h, d): t) =
    Format.fprintf fmt "{ %a }, (%a)"
      (ExpMap.make_pp S.pp) h
      (pp_opt Expr.pp) d

  let show s = Format.asprintf "%a" pp s

  type c_fix_t =
  | SubFix of Expr.t * S.c_fix_t
  [@@deriving show]

  type err_t =
  | MissingCell of Expr.t
  | NotAllocated of Expr.t
  | AlreadyAllocated of Expr.t
  | InvalidIndexValue of Expr.t
  | SubError of Expr.t * S.err_t
  [@@deriving show, yojson]

  type action =
  | Alloc
  | SubAction of S.action

  let action_from_str = function
  | "alloc" -> Some Alloc
  | s -> Option.map (fun a -> SubAction a) (S.action_from_str s)

  type pred =
  | SubPred of S.pred
  let pred_from_str s = Option.map (fun p -> SubPred p) (S.pred_from_str s)
  let pred_to_str = function
  | SubPred p -> S.pred_to_str p

  let init (): t = (ExpMap.empty, None)

  let clear s = s

  let validate_index ((h, d): t) idx =
    let open Delayed.Syntax in
    let* valid_idx = I.is_valid_index idx in
    if valid_idx = false
    then DR.error (InvalidIndexValue idx)
    else
      let* match_val = ExpMap.sym_find_opt idx h in
      match match_val, d with
      | Some (idx, v), _ -> DR.ok (idx, v)
      | None, None -> DR.error (MissingCell idx)
      | None, Some d ->
        if%sat Formula.SetMem (idx, d)
        then DR.error (NotAllocated idx)
        else DR.error (MissingCell idx)

  let modify_domain f d =
    match d with
    | None -> d
    | Some (Expr.ESet d) -> Some (Expr.ESet (f d))
    | Some _ -> failwith "Invalid index set"

  let update_entry (h, d) idx s =
    if S.is_empty s
    then (ExpMap.remove idx h, d)
    else (ExpMap.add idx s h, d)

  let execute_action action ((h, d): t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match action, args with
    | SubAction action, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args ->
      let** (idx, s) = validate_index (h, d) idx in
      let+ r = S.execute_action action s args in (
      match r with
      | Ok (s', v) -> Ok (update_entry (h, d) idx s', v)
      | Error e -> Error (SubError (idx, e)))
    | Alloc, _ ->
      let+* idx = match args, I.mode with
      | [], `Static -> let+ idx = I.make_fresh () in Ok idx
      | [idx], `Dynamic ->
        (* Check index is valid, and is not already allocated *)
        let* valid_idx = I.is_valid_index idx in
        if valid_idx = false
        then DR.error (InvalidIndexValue idx)
        else let+ found_val = ExpMap.sym_find_opt idx h in (
          match found_val with
          | Some _ -> Error (AlreadyAllocated idx)
          | None -> Ok idx)
      | _ -> failwith "Invalid number of arguments for allocation" in
      let s = S.init () in
      let h' = ExpMap.add idx s h in
      let d' = modify_domain (fun d -> idx :: d) d in
      Ok ((h', d'), [idx])

  let consume pred ((h, d): t) (args: Expr.t list): (t * Expr.t list, err_t) DR.t =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match pred, args with
    | SubPred pred, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: args ->
      let** (idx, s) = validate_index (h, d) idx in
      let+ r = S.consume pred s args in (
      match r with
      | Ok (s', v) -> Ok (update_entry (h, d) idx s', v)
      | Error e -> Error (SubError (idx, e)))

  let produce pred (h, d) args =
    let open Delayed.Syntax in
    match pred, args with
    | SubPred pred, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: args ->
      let* r = validate_index (h, d) idx in
      match r with
      | Ok (idx, s) ->
        let+ s' = S.produce pred s args in
        update_entry (h, d) idx s'
      | Error (MissingCell idx) ->
        let s = S.init () in
        let+ s' = S.produce pred s args in
        update_entry (h, d) idx s'
      | Error _ -> Delayed.vanish ()

  let compose s1 s2 = failwith "Implement here (compose)"
  let is_fully_owned s = failwith "Implement here (is_fully_owned)"
  let is_empty s = failwith "Implement here (is_empty)"

  let substitution_in_place sub (h, d) =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub idx ~partial:true in (idx', s') in
    let map_entries = ExpMap.bindings h in
    let* sub_entries = Delayed.all (List.map mapper map_entries) in
    let merger acc (idx, s) =
      let* acc = acc in
      let+ matching = ExpMap.sym_find_opt idx acc in
      match matching with
      | Some (idx, s') -> ExpMap.add idx (S.compose s s') acc
      | None -> ExpMap.add idx s acc in
    let+ h' = List.fold_left merger (Delayed.return ExpMap.empty) sub_entries in
    (h', d)

  let lvars (h, d) =
    let open Containers.SS in
    let lvars_map = ExpMap.fold (fun _ s acc -> union acc (S.lvars s)) h empty in
    match d with
    | None -> lvars_map
    | Some d -> union lvars_map (Expr.lvars d)

  let alocs (h, d) =
    let open Containers.SS in
    let alocs_map = ExpMap.fold (fun _ s acc -> union acc (S.alocs s)) h empty in
    match d with
    | None -> alocs_map
    | Some d -> union alocs_map (Expr.alocs d)

  let assertions (h, d) =
    let subasrts = ExpMap.fold (fun _ s acc -> S.assertions s @ acc) h [] in
    List.map (fun (a, i, o) -> (SubPred a, i, o)) subasrts

  let get_recovery_tactic (h, d) = function
    | SubError (idx, e) -> S.get_recovery_tactic (ExpMap.find idx h) e
    | _ -> Gillian.General.Recovery_tactic.none

  let get_fixes (h, d) pfs tenv = function
    | SubError (idx, e) ->
      let fixes = S.get_fixes (ExpMap.find idx h) pfs tenv e in
      List.map (fun (f, fs, vs, ss) -> (List.map (fun f -> SubFix (idx, f)) f, fs, vs, ss)) fixes
    | _ -> failwith "Implement here (get_fixes)"

  let can_fix = function
    | SubError (_, e) -> S.can_fix e
    | _ -> false (* TODO *)

  let apply_fix (h, d) f =
    let open Delayed.Syntax in
    match f with
    | SubFix (idx, f) ->
      let s = ExpMap.find idx h in
      let+ r = S.apply_fix s f in
      (match r with
      | Ok s' -> Ok (ExpMap.add idx s' h, d)
      | Error e -> Error (SubError (idx, e)))

end
