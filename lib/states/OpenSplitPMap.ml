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

  (** Concrete pairs, symbolic(/mixed?) pairs *)
  type entry = S.t [@@deriving yojson]

  type t = entry ExpMap.t * S.t ExpMap.t [@@deriving yojson]

  let pp fmt ((ch, sh) : t) =
    let h =
      ExpMap.union
        (fun k sv cv ->
          Logging.tmi (fun f ->
              f
                "Found clashing keys at %a in SplitPMap ?? Defaulting to \
                 symbolic ! Values %a and %a"
                Expr.pp k S.pp sv S.pp cv);
          Some sv)
        ch sh
    in
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a" (ExpMap.make_pp S.pp) h;
    Format.pp_close_box fmt ()

  type err_t =
    | NotAllocated of Expr.t
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

  let empty () : t = (ExpMap.empty, ExpMap.empty)

  let validate_index ((ch, sh) : t) idx =
    let open Delayed.Syntax in
    let* idx' = I.is_valid_index idx in
    match idx' with
    | None -> DR.error (InvalidIndexValue idx)
    | Some idx' -> (
        (* This check might not be needed if we know idx' is not concrete *)
        match ExpMap.find_opt idx' ch with
        | Some v -> DR.ok (idx', v)
        | None -> (
            match ExpMap.find_opt idx' sh with
            | Some v -> DR.ok (idx', v)
            | None ->
                let merged = ExpMap.union (fun _ v1 _ -> Some v1) ch sh in
                let+ match_val = ExpMap.sym_find_opt idx' merged in
                Option.value ~default:(idx', S.empty ()) match_val |> Result.ok)
        )

  let update_entry (ch, sh) idx idx' s =
    (* remove from both (dont know where it was) *)
    let ch', sh' = (ExpMap.remove idx ch, ExpMap.remove idx sh) in
    if S.is_empty s then (ch', sh')
    else if Expr.is_concrete idx' && S.is_concrete s then
      (ExpMap.add idx' s ch', sh')
    else (ch', ExpMap.add idx' s sh')

  let execute_action action (s : t) args =
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
        let s' = update_entry s idx idx ss in
        Ok (s', idx :: v)

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
        let*? idx', ss = validate_index s idx in
        let+ ss' = S.produce pred ss args in
        update_entry s idx idx' ss'

  let compose (ch1, sh1) (ch2, sh2) =
    let open Delayed.Syntax in
    (* This is not sound, we don't take into account when, eg,
       ch1 has [i -> x] and sh2 has [i -> y], where we need to compose
       x • y and check if it's concrete. *)
    let* ch = ExpMap.sym_merge S.compose ch1 ch2 in
    let+ sh = ExpMap.sym_merge S.compose sh1 sh2 in
    (ch, sh)

  let is_exclusively_owned _ _ = Delayed.return false

  let is_empty = function
    | ch, sh ->
        ExpMap.for_all (fun _ s -> S.is_empty s) ch
        && ExpMap.for_all (fun _ s -> S.is_empty s) sh

  let is_concrete (_, sh) = ExpMap.is_empty sh

  let instantiate = function
    | [] -> ((ExpMap.empty, ExpMap.empty), [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub (ch, sh) =
    let open Delayed.Syntax in
    let subst = Subst.subst_in_expr sub ~partial:true in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = subst idx in
      (idx', s')
    in
    let map_entries = ExpMap.bindings sh in
    let* sub_entries = Delayed.all (List.map mapper map_entries) in
    let ch_new, sh_new =
      List.partition
        (fun (k, v) -> Expr.is_concrete k && S.is_concrete v)
        sub_entries
    in
    let* ch' = ExpMap.sym_compose S.compose ch_new ch in
    let+ sh' = ExpMap.sym_compose S.compose sh_new ExpMap.empty in
    (ch', sh')

  let lvars (ch, sh) =
    let open Containers.SS in
    let folder _ s acc = union acc (S.lvars s) in
    let lvars_map = ExpMap.fold folder ch empty in
    ExpMap.fold folder sh lvars_map

  let alocs (ch, sh) =
    let open Containers.SS in
    let folder _ s acc = union acc (S.alocs s) in
    let alocs_map = ExpMap.fold folder ch empty in
    ExpMap.fold folder sh alocs_map

  let lift_corepred k (p, i, o) = (p, k :: i, o)

  let assertions (ch, sh) =
    let folder k s acc = (List.map (lift_corepred k)) (S.assertions s) @ acc in
    let sub_assrts = ExpMap.fold folder ch [] in
    ExpMap.fold folder sh sub_assrts

  let assertions_others (ch, sh) =
    List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings ch)
    @ List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings sh)

  let get_recovery_tactic = function
    | SubError (_, idx, e) ->
        Gillian.General.Recovery_tactic.merge (S.get_recovery_tactic e)
          (Gillian.General.Recovery_tactic.try_unfold [ idx ])
    | NotAllocated idx | InvalidIndexValue idx ->
        Gillian.General.Recovery_tactic.try_unfold [ idx ]

  let can_fix = function
    | SubError (_, _, e) -> S.can_fix e
    | InvalidIndexValue _ -> false
    | NotAllocated _ -> false

  let get_fixes = function
    | SubError (idx, idx', e) ->
        let open Formula.Infix in
        S.get_fixes e
        |> MyUtils.deep_map (MyAsrt.map_cp (lift_corepred idx'))
        |> List.map (fun f -> f @ [ MyAsrt.Pure idx #== idx' ])
    | _ -> failwith "Called get_fixes on unfixable error"
end

module Make (I : PMapIndex) (S : MyMonadicSMemory.S) :
  OpenPMap.OpenPMapType
    with type entry = S.t
     and type t = S.t MyUtils.ExpMap.t * S.t MyUtils.ExpMap.t =
  Make_ (I) (S) (MyUtils.ExpMap)

module MakeEnt (I : PMapIndex) (S : MyMonadicSMemory.S) :
  OpenPMap.OpenPMapType
    with type entry = S.t
     and type t = S.t MyUtils.ExpMapEnt.t * S.t MyUtils.ExpMapEnt.t =
  Make_ (I) (S) (MyUtils.ExpMapEnt)
