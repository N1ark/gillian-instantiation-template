open Gillian.Utils
open Gillian.Monadic
open Gil_syntax
module Subst = Gillian.Symbolic.Subst
module DR = Delayed_result

module type PMapIndex = PMap.PMapIndex

module StringIndex = PMap.StringIndex
module LocationIndex = PMap.LocationIndex
module SS = Gillian.Utils.Containers.SS

module SMap = Gillian.Utils.Prelude.Map.Make (struct
  include String

  let of_yojson = function
    | `String s -> Ok s
    | _ -> Error "string_of_yojson: expected string"

  let to_yojson s = `String s
end)

module Make (S : MyMonadicSMemory.S) = struct
  type entry = S.t [@@deriving yojson]
  type t = entry SMap.t [@@deriving yojson]

  let pp fmt (h : t) =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a"
      (MyUtils.pp_bindings ~pp_k:Fmt.string ~pp_v:S.pp SMap.iter)
      h;
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

  let empty () : t = SMap.empty

  let get_loc_fast = function
    | Expr.Lit (Loc loc) -> loc
    | Expr.ALoc loc -> loc
    | _ -> failwith "Non-trivial location given to get_loc_fast"

  let get_loc idx =
    MyUtils.get_loc idx |> Delayed_option.to_dr ~none:(InvalidIndexValue idx)

  let validate_index (h : t) idx =
    let open Delayed.Syntax in
    let* idx_s = MyUtils.get_loc idx in
    match idx_s with
    | Some s ->
        let idx_e = Expr.loc_from_loc_name s in
        let res = SMap.find_opt s h in
        let res = Option.value ~default:(S.empty ()) res in
        DR.ok (idx_e, res)
    | None -> DR.error (InvalidIndexValue idx)

  (* ignore the 2nd parameter, but keep it for signature parity with PMap/SplitPMap *)
  let update_entry h _ idx s =
    let idx_s = get_loc_fast idx in
    if S.is_empty s then SMap.remove idx_s h else SMap.add idx_s s h

  let execute_action action (s : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let** idx', ss = validate_index s idx in
        let+ r = S.execute_action action ss args in
        match r with
        | Ok (ss', v) -> Ok (update_entry s () idx' ss', idx' :: v)
        | Error e -> Error (SubError (idx, idx', e)))
    | Alloc, args ->
        let idx = Expr.ALoc (ALoc.alloc ()) in
        let ss, v = S.instantiate args in
        let s' = update_entry s () idx ss in
        DR.ok (s', idx :: v)

  let consume pred s ins =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match ins with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: ins -> (
        let** idx', ss = validate_index s idx in
        let+ r = S.consume pred ss ins in
        match r with
        | Ok (ss', v) -> Ok (update_entry s () idx' ss', v)
        | Error e -> Error (SubError (idx, idx', e)))

  let produce pred s args =
    let open Delayed.Syntax in
    let open MyUtils.Syntax in
    match args with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: args ->
        let*? idx', ss = validate_index s idx in
        let+ ss' = S.produce pred ss args in
        update_entry s () idx' ss'

  let compose h1 h2 =
    let open Delayed.Syntax in
    let compose_binding m (k, v) =
      let* m = m in
      match SMap.find_opt k m with
      | Some v' ->
          let+ v'' = S.compose v v' in
          SMap.add k v'' m
      | None -> Delayed.return (SMap.add k v m)
    in
    List.fold_left compose_binding (Delayed.return h1) (SMap.bindings h2)

  let is_exclusively_owned _ _ = Delayed.return false

  let is_empty = function
    | h -> SMap.for_all (fun _ s -> S.is_empty s) h

  let is_concrete h = SMap.for_all (fun _ s -> S.is_concrete s) h

  let instantiate = function
    | [] -> (SMap.empty, [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub h =
    let open Delayed.Syntax in
    let aloc_subst =
      Subst.fold sub
        (fun l r acc ->
          match l with
          | ALoc aloc -> (aloc, r) :: acc
          | _ -> acc)
        []
    in
    let* substituted =
      SMap.fold
        (fun k v acc ->
          let* acc = acc in
          let+ s' = S.substitution_in_place sub v in
          SMap.add k s' acc)
        h
        (Delayed.return SMap.empty)
    in
    List.fold_left
      (fun acc (idx, idx') ->
        let* acc = acc in
        match SMap.find_opt idx acc with
        | None -> Delayed.return acc
        | Some s -> (
            let idx' = get_loc_fast idx' in
            match SMap.find_opt idx' acc with
            | None -> Delayed.return (SMap.remove idx acc |> SMap.add idx' s)
            | Some s' ->
                let+ s'' = S.compose s s' in
                SMap.remove idx acc |> SMap.add idx' s''))
      (Delayed.return substituted)
      aloc_subst

  let lvars h =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.lvars s)) h empty

  let alocs h =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.alocs s)) h empty

  let lift_corepred k (p, i, o) = (p, k :: i, o)

  let assertions h =
    let folder k s acc =
      (List.map @@ lift_corepred @@ Expr.loc_from_loc_name k) (S.assertions s)
      @ acc
    in
    SMap.fold folder h []

  let assertions_others h =
    List.concat_map (fun (_, v) -> S.assertions_others v) (SMap.bindings h)

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
