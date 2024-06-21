open Gillian.Utils
open Gillian.Monadic
open Gil_syntax
module Subst = Gillian.Symbolic.Subst
module DR = Delayed_result
module ExpMap = MyUtils.ExpMap

module MyString = struct
  include String

  let to_yojson s = `String s

  let of_yojson = function
    | `String s -> Ok s
    | _ -> Error "Expected string"
end

module SMap = Prelude.Map.Make (MyString)

(** Similar to PMap, but only supports GIL abstract locations. *)
module Make (S : MyMonadicSMemory.S) : MyMonadicSMemory.S = struct
  type t = S.t ExpMap.t [@@deriving yojson]

  let pp fmt (h : t) =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a"
      (MyUtils.pp_bindings ~pp_k:Expr.pp ~pp_v:S.pp ExpMap.iter)
      h;
    Format.pp_close_box fmt ()

  let show s = Format.asprintf "%a" pp s

  type c_fix_t = SubFix of Expr.t * S.c_fix_t [@@deriving show]

  type err_t =
    | MissingCell of Expr.t
    | NotAllocated of Expr.t
    | InvalidIndexValue of Expr.t
    | SubError of Expr.t * S.err_t
  [@@deriving show, yojson]

  type action = Alloc | SubAction of S.action

  let action_from_str = function
    | "alloc" -> Some Alloc
    | s -> Option.map (fun a -> SubAction a) (S.action_from_str s)

  let action_to_str = function
    | SubAction a -> S.action_to_str a
    | Alloc -> "alloc"

  let list_actions () =
    [ (Alloc, [ "params" ], [ "address" ]) ]
    @ List.map
        (fun (a, args, ret) -> (SubAction a, "index" :: args, ret))
        (S.list_actions ())

  type pred = S.pred

  let pred_from_str = S.pred_from_str
  let pred_to_str = S.pred_to_str

  let list_preds () =
    List.map (fun (p, ins, outs) -> (p, "index" :: ins, outs)) (S.list_preds ())

  let empty () : t = ExpMap.empty

  let validate_index (h : t) idx =
    match idx with
    | Expr.Lit (Loc _) | Expr.ALoc _ -> (
        match ExpMap.find_opt idx h with
        | Some v -> DR.ok (idx, v)
        | None -> DR.error (MissingCell idx))
    | _ -> (
        let open Delayed.Syntax in
        let* idx' = Delayed.resolve_loc idx in
        match idx' with
        | None -> DR.error (InvalidIndexValue idx)
        | Some idx' -> (
            let idx' = Expr.loc_from_loc_name idx' in
            let* match_val = ExpMap.sym_find_opt idx' h in
            match match_val with
            | Some (_, idx', v) -> DR.ok (idx', v)
            | None -> DR.error (MissingCell idx')))

  let update_entry h idx s =
    if S.is_empty s then ExpMap.remove idx h else ExpMap.add idx s h

  let execute_action action (h : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let** idx, s = validate_index h idx in
        let+ r = S.execute_action action s args in
        match r with
        | Ok (s', v) ->
            Ok (update_entry h idx s', if List.is_empty v then v else idx :: v)
        | Error e -> Error (SubError (idx, e)))
    | Alloc, args ->
        let idx = ALoc.alloc () in
        let idx = Expr.loc_from_loc_name idx in
        let s, v = S.instantiate args in
        let h' = ExpMap.add idx s h in
        DR.ok (h', idx :: v)

  let consume pred h ins =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match ins with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: ins -> (
        let** idx, s = validate_index h idx in
        let+ r = S.consume pred s ins in
        match r with
        | Ok (s', v) -> Ok (update_entry h idx s', v)
        | Error e -> Error (SubError (idx, e)))

  let produce pred h args =
    let open Delayed.Syntax in
    match args with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: args -> (
        let* r = validate_index h idx in
        match r with
        | Ok (idx, s) ->
            let+ s' = S.produce pred s args in
            update_entry h idx s'
        | Error (MissingCell idx) ->
            let s = S.empty () in
            let+ s' = S.produce pred s args in
            update_entry h idx s'
        | Error (InvalidIndexValue v) ->
            let s = S.empty () in
            let loc = ALoc.alloc () in
            let loc = Expr.loc_from_loc_name loc in
            let* s' = S.produce pred s args in
            Delayed.return
              ~learned:[ Formula.Infix.(loc #== v) ]
              (update_entry h loc s')
        | Error _ -> Delayed.vanish ())

  let compose _ _ = failwith "Implement here (compose)"

  let is_fully_owned h =
    let open Formula.Infix in
    ExpMap.fold (fun _ s acc -> acc #&& (S.is_fully_owned s)) h Formula.True

  let is_empty h = ExpMap.for_all (fun _ s -> S.is_empty s) h

  let instantiate = function
    | [] -> (ExpMap.empty, [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub h =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub idx ~partial:true in
      (idx', s')
    in
    let map_entries = ExpMap.bindings h in
    let* sub_entries = Delayed.all (List.map mapper map_entries) in
    ExpMap.sym_compose S.compose sub_entries ExpMap.empty

  let lvars h =
    let open Containers.SS in
    ExpMap.fold
      (fun k s acc -> union acc (union (Expr.lvars k) (S.lvars s)))
      h empty

  let alocs h =
    let open Containers.SS in
    ExpMap.fold
      (fun k s acc -> union acc (union (Expr.alocs k) (S.alocs s)))
      h empty

  let assertions h =
    let pred_wrap k (p, i, o) = (p, k :: i, o) in
    let folder k s acc = (List.map (pred_wrap k)) (S.assertions s) @ acc in
    ExpMap.fold folder h []

  let get_recovery_tactic h = function
    | SubError (idx, e) -> S.get_recovery_tactic (ExpMap.find idx h) e
    | _ -> Gillian.General.Recovery_tactic.none

  let get_fixes h pfs tenv = function
    | SubError (idx, e) ->
        let fixes = S.get_fixes (ExpMap.find idx h) pfs tenv e in
        List.map
          (fun (f, fs, vs, ss) ->
            (List.map (fun f -> SubFix (idx, f)) f, fs, vs, ss))
          fixes
    | _ -> failwith "Implement here (get_fixes)"

  let can_fix = function
    | SubError (_, e) -> S.can_fix e
    | _ -> false (* TODO *)

  let apply_fix h f =
    let open Delayed.Syntax in
    match f with
    | SubFix (idx, f) -> (
        let s = ExpMap.find idx h in
        let+ r = S.apply_fix s f in
        match r with
        | Ok s' -> Ok (ExpMap.add idx s' h)
        | Error e -> Error (SubError (idx, e)))
end
