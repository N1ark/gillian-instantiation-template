open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

module type PMapIndex = PMap.PMapIndex

module Make_
    (I : PMapIndex)
    (S : MyMonadicSMemory.S)
    (ExpMap : MyUtils.SymExprMap) =
struct
  if I.mode = Dynamic then
    failwith "Dynamic mode is not supported for OpenPMap. Use PMap instead."

  type entry = S.t [@@deriving yojson]
  type t = entry ExpMap.t [@@deriving yojson]

  let pp fmt h =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a" (ExpMap.make_pp S.pp) h;
    Format.pp_close_box fmt ()

  type err_t =
    | InvalidIndexValue of Expr.t
    | SubError of
        Expr.t * Expr.t * S.err_t (* Original index, map index, error *)
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

  let validate_index h idx =
    let open Delayed.Syntax in
    let* idx' = I.is_valid_index idx in
    match idx' with
    | None -> DR.error (InvalidIndexValue idx)
    | Some idx' ->
        let+ match_val = ExpMap.sym_find_opt idx' h in
        Ok (Option.value ~default:(idx', S.empty ()) match_val)

  let domain_add _ s = s

  let update_entry h idx idx' s =
    if S.is_empty s then ExpMap.remove idx h
    else if Expr.equal idx idx' then ExpMap.add idx s h
    else ExpMap.remove idx h |> ExpMap.add idx' s

  let execute_action action s args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let** idx', ss = validate_index s idx in
        let+ r = S.execute_action action ss args in
        match r with
        | Ok (ss', v) -> Ok (update_entry s idx idx' ss', idx' :: v)
        | Error e -> Error (SubError (idx, idx', e)))
    | Alloc, args ->
        let+ idx = I.make_fresh () in
        let ss, v = S.instantiate args in
        Ok (update_entry s idx idx ss, idx :: v)

  let consume pred s ins =
    let open DR.Syntax in
    let open Delayed.Syntax in
    match ins with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: ins -> (
        let** idx', ss = validate_index s idx in
        let+ r = S.consume pred ss ins in
        match r with
        | Ok (ss', v) -> Ok (update_entry s idx idx' ss', v)
        | Error e -> Error (SubError (idx, idx', e)))

  let produce pred s args =
    let open Delayed.Syntax in
    let open MyUtils.Syntax in
    match args with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: args ->
        let*? idx, ss = validate_index s idx in
        let+ ss' = S.produce pred ss args in
        update_entry s idx idx ss'

  let compose = ExpMap.sym_merge S.compose
  let is_exclusively_owned _ _ = Delayed.return false
  let is_empty = ExpMap.for_all (fun _ s -> S.is_empty s)
  let is_concrete = ExpMap.for_all (fun _ s -> S.is_concrete s)

  let instantiate = function
    | [] -> (ExpMap.empty, [])
    | [ Expr.EList fields ] ->
        let ss, _ = S.instantiate [] in
        let h =
          List.fold_left (fun acc k -> ExpMap.add k ss acc) ExpMap.empty fields
        in
        (h, [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub h =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub ~partial:true idx in
      (idx', s')
    in
    let* sub_entries = ExpMap.bindings h |> List.map mapper |> Delayed.all in
    ExpMap.sym_compose S.compose sub_entries ExpMap.empty

  let lvars h =
    let open Containers.SS in
    ExpMap.fold
      (fun k s acc -> S.lvars s |> union @@ Expr.lvars k |> union acc)
      h empty

  let alocs h =
    let open Containers.SS in
    ExpMap.fold (fun _ s acc -> S.alocs s |> union acc) h empty

  let lift_corepred k (p, i, o) = (p, k :: i, o)

  let assertions h =
    ExpMap.fold
      (fun k v acc -> (S.assertions v |> List.map @@ lift_corepred k) @ acc)
      h []

  let assertions_others h =
    List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings h)

  let get_recovery_tactic = function
    | SubError (_, idx, e) ->
        Gillian.General.Recovery_tactic.merge (S.get_recovery_tactic e)
          (Gillian.General.Recovery_tactic.try_unfold [ idx ])
    | InvalidIndexValue idx ->
        Gillian.General.Recovery_tactic.try_unfold [ idx ]

  let can_fix = function
    | SubError (_, _, e) -> S.can_fix e
    | InvalidIndexValue _ -> false

  let get_fixes = function
    | SubError (idx, idx', e) ->
        let open Formula.Infix in
        S.get_fixes e
        |> MyUtils.deep_map @@ MyAsrt.map_cp @@ lift_corepred idx'
        |> List.map (fun f -> MyAsrt.Pure idx #== idx' :: f)
    | _ -> failwith "Called get_fixes on unfixable error"
end

module Make (I : PMapIndex) (S : MyMonadicSMemory.S) =
  Make_ (I) (S) (MyUtils.ExpMap)

module MakeEnt (I : PMapIndex) (S : MyMonadicSMemory.S) =
  Make_ (I) (S) (MyUtils.ExpMapEnt)

module type OpenPMapType = sig
  include MyMonadicSMemory.S

  type entry

  val validate_index : t -> Expr.t -> (Expr.t * entry, err_t) DR.t
  val update_entry : t -> Expr.t -> Expr.t -> entry -> t
end
