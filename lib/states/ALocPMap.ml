open Gillian.Utils
open Gillian.Monadic
open Gil_syntax
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
  type t = S.t SMap.t * SS.t option [@@deriving yojson]

  let pp fmt ((h, d) : t) =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a"
      (MyUtils.pp_bindings ~pp_k:Fmt.string ~pp_v:S.pp SMap.iter)
      h;
    Format.pp_close_box fmt ();
    match d with
    | None -> Format.fprintf fmt "@\nDomainSet: None"
    | Some d ->
        let l = SS.to_list d in
        let l' = List.sort String.compare l in
        Format.fprintf fmt "@\nDomainSet: -{ %a }-"
          Fmt.(list ~sep:comma string)
          l'

  type err_t =
    | NotAllocated of string
    | InvalidIndexValue of Expr.t
    | MissingDomainSet
    | DomainSetNotFullyOwned
    | SubError of
        Expr.t * string * S.err_t (* Original index, map index, error *)
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

  type pred = DomainSet | SubPred of S.pred

  let pred_from_str = function
    | "domainset" -> Some DomainSet
    | s -> Option.map (fun p -> SubPred p) (S.pred_from_str s)

  let pred_to_str = function
    | SubPred p -> S.pred_to_str p
    | DomainSet -> "domainset"

  let list_preds () =
    (DomainSet, [], [ "domainset" ])
    :: List.map
         (fun (p, ins, outs) -> (SubPred p, "index" :: ins, outs))
         (S.list_preds ())

  let empty () : t = (SMap.empty, None)

  let get_loc =
    let open Delayed.Syntax in
    function
    | Expr.Lit (Loc loc) -> DR.ok loc
    | Expr.ALoc loc -> DR.ok loc
    | Expr.LVar _ as v -> (
        let* loc = Delayed.resolve_loc v in
        match loc with
        | Some loc -> DR.ok loc
        | None ->
            let loc_name = ALoc.alloc () in
            DR.ok ~learned:[ Formula.Eq (v, ALoc loc_name) ] loc_name)
    | le -> DR.error (InvalidIndexValue le)

  let domain_to_expr d =
    Expr.ESet (SS.to_list d |> List.map Expr.loc_from_loc_name)

  let modify_domain f d =
    match d with
    | None -> d
    | Some d -> Some (f d)

  let validate_index ((h, d) : t) idx =
    let open DR.Syntax in
    let** idx_s = get_loc idx in
    let res = SMap.find_opt idx_s h in
    match (res, d) with
    | Some v, _ -> DR.ok (idx_s, v)
    (* If the cell is not found, it is initialised to empty. Trust the below state
       models to raise a Miss error, that will then be wrapped and taken care of.
       Otherwise we would need to raise a miss error that doesn't make sense since it can't
       really be fixed; there is no 'cell' predicate in the PMap, it relies on the sub
       states' predicates being extended with an index in-argument. *)
    | None, None -> DR.ok (idx_s, S.empty ())
    | None, Some d when SS.mem idx_s d -> DR.ok (idx_s, S.empty ())
    | None, Some _ -> DR.error (NotAllocated idx_s)

  let update_entry (h, d) idx s =
    if S.is_empty s then (SMap.remove idx h, d) else (SMap.add idx s h, d)

  let execute_action action ((h, d) : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let** idx_s, s = validate_index (h, d) idx in
        let+ r = S.execute_action action s args in
        match r with
        | Ok (s', v) ->
            Ok (update_entry (h, d) idx_s s', Expr.loc_from_loc_name idx_s :: v)
        | Error e -> Error (SubError (idx, idx_s, e)))
    | Alloc, args ->
        let idx = ALoc.alloc () in
        let s, v = S.instantiate args in
        let h' = SMap.add idx s h in
        let d' = modify_domain (SS.add idx) d in
        DR.ok ((h', d'), Expr.ALoc idx :: v)

  let consume pred (h, d) ins =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (pred, ins) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: ins -> (
        let** idx_s, s = validate_index (h, d) idx in
        let+ r = S.consume pred s ins in
        match r with
        | Ok (s', v) -> Ok (update_entry (h, d) idx_s s', v)
        | Error e -> Error (SubError (idx, idx_s, e)))
    | DomainSet, [] -> (
        match d with
        | Some d -> DR.ok ((h, None), [ domain_to_expr d ])
        | None -> DR.error MissingDomainSet)
    | DomainSet, _ -> failwith "Invalid number of ins for domainset"

  let produce pred (h, d) args =
    let open Delayed.Syntax in
    let open MyUtils in
    match (pred, args) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: args ->
        let*? idx_s, s = validate_index (h, d) idx in
        let+ s' = S.produce pred s args in
        update_entry (h, d) idx_s s'
    | DomainSet, [ Expr.ESet d' ] ->
        if Option.is_some d then Delayed.vanish ()
        else
          let rec parse_domainset d ls =
            match ls with
            | [] -> Delayed.return d
            | loc :: tl ->
                let*? loc_name = get_loc loc in
                parse_domainset (SS.add loc_name d) tl
          in
          let+ d' = parse_domainset SS.empty d' in
          (h, Some d')
    | DomainSet, _ -> failwith "Invalid arguments for domainset produce"

  let compose (h1, d1) (h2, d2) =
    let open Delayed.Syntax in
    let* d' =
      match (d1, d2) with
      | d1, None -> Delayed.return d1
      | None, d2 -> Delayed.return d2
      | _, _ -> Delayed.vanish ()
    in
    let compose_binding m (k, v) =
      let* m = m in
      match SMap.find_opt k m with
      | Some v' ->
          let+ v'' = S.compose v v' in
          SMap.add k v'' m
      | None -> Delayed.return (SMap.add k v m)
    in
    let+ h' =
      List.fold_left compose_binding (Delayed.return h1) (SMap.bindings h2)
    in
    (h', d')

  let is_fully_owned s e =
    let open Formula.Infix in
    match s with
    | h, Some _ ->
        SMap.fold (fun _ s acc -> acc #&& (S.is_fully_owned s e)) h Formula.True
    | _, None -> Formula.False

  let is_empty = function
    | _, Some _ -> false
    | h, None -> SMap.for_all (fun _ s -> S.is_empty s) h

  let instantiate = function
    | [] -> ((SMap.empty, Some SS.empty), [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub (h, d) =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      (idx, s')
    in
    let map_entries = SMap.bindings h in
    let+ sub_entries = Delayed.all (List.map mapper map_entries) in
    let h' = SMap.of_list sub_entries in
    (h', d)

  let lvars (h, _) =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.lvars s)) h empty
  (* I don't think the domain can have any lvars? *)

  let alocs (h, d) =
    let open Containers.SS in
    let alocs_map = SMap.fold (fun _ s acc -> union acc (S.alocs s)) h empty in
    match d with
    | None -> alocs_map
    | Some d ->
        let domain_exprs = SS.to_list d |> List.map Expr.loc_from_loc_name in
        let alocs_domain =
          List.fold_left
            (fun acc e -> union acc (Expr.alocs e))
            empty domain_exprs
        in
        union alocs_map alocs_domain

  let lift_corepred k (p, i, o) = (SubPred p, Expr.loc_from_loc_name k :: i, o)

  let assertions (h, d) =
    let folder k s acc = (List.map (lift_corepred k)) (S.assertions s) @ acc in
    let sub_assrts = SMap.fold folder h [] in
    match d with
    | None -> sub_assrts
    | Some d -> (DomainSet, [], [ domain_to_expr d ]) :: sub_assrts

  let assertions_others (h, _) =
    List.concat_map (fun (_, v) -> S.assertions_others v) (SMap.bindings h)

  let get_recovery_tactic (h, _) = function
    | SubError (_, idx', e) ->
        let s = SMap.find_opt idx' h |> Option.value ~default:(S.empty ()) in
        S.get_recovery_tactic s e
    | _ -> Gillian.General.Recovery_tactic.none

  let can_fix = function
    | SubError (_, _, e) -> S.can_fix e
    | MissingDomainSet -> true
    | _ -> false (* TODO *)

  let get_fixes = function
    | SubError (idx, idx', e) ->
        let open Formula.Infix in
        S.get_fixes e
        |> MyUtils.deep_map (MyAsrt.map_cp (lift_corepred idx'))
        |> List.map (fun f ->
               f @ [ MyAsrt.Pure idx #== (Expr.loc_from_loc_name idx') ])
    | MissingDomainSet ->
        let lvar = LVar.alloc () in
        [
          [
            MyAsrt.CorePred (DomainSet, [], [ Expr.LVar lvar ]);
            MyAsrt.Types [ (lvar, Type.SetType) ];
          ];
        ]
    | _ -> failwith "Called get_fixes on unfixable error"
end
