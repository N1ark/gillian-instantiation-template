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
  (** Concrete pairs, symbolic(/mixed?) pairs, domain set *)
  type entry = S.t [@@deriving yojson]

  type t = entry ExpMap.t * S.t ExpMap.t * Expr.t option [@@deriving yojson]

  let pp fmt ((ch, sh, d) : t) =
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
    Format.pp_close_box fmt ();
    match d with
    | None -> Format.fprintf fmt "@\nDomainSet: None"
    | Some (Expr.ESet l) ->
        let l' = List.sort Expr.compare l in
        Format.fprintf fmt "@\nDomainSet: -{ %a }-"
          (Fmt.list ~sep:Fmt.comma Expr.pp)
          l'
    | Some d ->
        (* shouldn't happen *)
        Format.fprintf fmt "@\nDomainSet: %a" Expr.pp d

  type err_t =
    | NotAllocated of Expr.t
    | InvalidIndexValue of Expr.t
    | MissingDomainSet
    | AllocDisallowedInDynamic
    | DomainSetNotFullyOwned
    | SubError of
        Expr.t * Expr.t * S.err_t (* Original index, map index, error *)
  [@@deriving show, yojson]

  type action = Alloc | GetDomainSet | SubAction of S.action

  let action_from_str = function
    | "alloc" -> Some Alloc
    | "get_domainset" -> Some GetDomainSet
    | s -> Option.map (fun a -> SubAction a) (S.action_from_str s)

  let action_to_str = function
    | SubAction a -> S.action_to_str a
    | Alloc -> "alloc"
    | GetDomainSet -> "get_domainset"

  let list_actions () =
    (match I.mode with
    | Static -> [ (Alloc, [ "params" ], [ "address" ]) ]
    | Dynamic -> [])
    @ [ (GetDomainSet, [], [ "domainset" ]) ]
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

  let empty () : t = (ExpMap.empty, ExpMap.empty, None)

  let domain_add idx (ch, sh, d) =
    match d with
    | None -> (ch, sh, d)
    | Some (Expr.ESet d) -> (ch, sh, Some (Expr.ESet (idx :: d)))
    | Some _ -> failwith "Invalid index set"

  let validate_index ((ch, sh, d) : t) idx =
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
            | None -> (
                let merged = ExpMap.union (fun _ v1 _ -> Some v1) ch sh in
                let* match_val = ExpMap.sym_find_opt idx' merged in
                match (match_val, d) with
                | Some (idx'', v), _ -> DR.ok (idx'', v)
                | None, None -> DR.ok (idx', S.empty ())
                | None, Some d ->
                    if%sat Formula.SetMem (idx', d) then DR.ok (idx', S.empty ())
                    else DR.error (NotAllocated idx'))))

  let update_entry (ch, sh, d) idx idx' s =
    (* remove from both (dont know where it was) *)
    let ch', sh' = (ExpMap.remove idx ch, ExpMap.remove idx sh) in
    if S.is_empty s then (ch', sh', d)
    else if Expr.is_concrete idx' && S.is_concrete s then
      (ExpMap.add idx' s ch', sh', d)
    else (ch', ExpMap.add idx' s sh', d)

  let execute_action action (s : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let* r = validate_index s idx in
        let** s', idx', ss =
          match r with
          | Ok (idx, ss) -> DR.ok (s, idx, ss)
          (* In Dynamic mode, missing cells are instantiated to a default value *)
          | Error (NotAllocated idx) when I.mode = Dynamic ->
              let ss, _ = S.instantiate I.default_instantiation in
              let s' = domain_add idx s in
              DR.ok (s', idx, ss)
          | Error e -> DR.error e
        in
        let+ r = S.execute_action action ss args in
        match r with
        | Ok (ss', v) -> Ok (update_entry s' idx idx' ss', idx' :: v)
        | Error e -> Error (SubError (idx, idx', e)))
    | Alloc, args -> (
        match I.mode with
        | Dynamic -> DR.error AllocDisallowedInDynamic
        | Static ->
            let idx = I.make_fresh () in
            let ss, v = S.instantiate args in
            let s' = update_entry s idx idx ss |> domain_add idx in
            DR.ok (s', idx :: v))
    | GetDomainSet, [] -> (
        match s with
        (* Implementation taken from JSIL:
           - ensure domain set is there
           - ensure the domain set is exactly the set of keys in the map
           - filter keys to remove empty cells (for JS: Nono)
           - return as a list *)
        | ch, sh, Some d ->
            (* CAREFUL HERE !! Overriding the symbolic side *)
            let h_merged = ExpMap.union (fun _ v1 _ -> Some v1) ch sh in
            let keys = List.map fst (ExpMap.bindings h_merged) in
            if%ent Formula.Infix.(d #== (Expr.ESet keys)) then
              let _, pos =
                ExpMap.partition (fun _ s -> S.is_empty s) h_merged
              in
              let keys = List.map fst (ExpMap.bindings pos) in
              DR.ok (s, [ Expr.list keys ])
            else DR.error DomainSetNotFullyOwned
        | _, _, None -> DR.error MissingDomainSet)
    | GetDomainSet, _ -> failwith "Invalid arguments for get_domainset"

  let consume pred s ins =
    let open Delayed.Syntax in
    match (pred, ins) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: ins -> (
        let* res = validate_index s idx in
        match (res, I.mode) with
        | Ok (idx', ss), _ -> (
            let+ r = S.consume pred ss ins in
            match r with
            | Ok (ss', v) -> Ok (update_entry s idx idx' ss', v)
            | Error e -> Error (SubError (idx, idx', e)))
        | Error (NotAllocated idx'), Dynamic -> (
            let ss, _ = S.instantiate I.default_instantiation in
            let+ r = S.consume pred ss ins in
            match r with
            | Ok (ss', v) ->
                let s' = update_entry s idx idx' ss' |> domain_add idx' in
                Ok (s', v)
            | Error e -> Error (SubError (idx, idx', e)))
        | Error e, _ -> DR.error e)
    | DomainSet, [] -> (
        match s with
        | ch, sh, Some d -> DR.ok ((ch, sh, None), [ d ])
        | _, _, None -> DR.error MissingDomainSet)
    | DomainSet, _ -> failwith "Invalid number of ins for domainset"

  let produce pred s args =
    let open Delayed.Syntax in
    let open MyUtils.Syntax in
    match (pred, args) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: args ->
        let*? idx', ss = validate_index s idx in
        let+ ss' = S.produce pred ss args in
        update_entry s idx idx' ss'
    | DomainSet, [ d' ] -> (
        match s with
        | _, _, Some _ -> Delayed.vanish ()
        | ch, sh, None ->
            Delayed.return (ch, sh, Some d') (* TODO: if%sat typeof set ?? *))
    | DomainSet, _ -> failwith "Invalid arguments for domainset produce"

  let compose (ch1, sh1, d1) (ch2, sh2, d2) =
    let open Delayed.Syntax in
    let* d =
      match (d1, d2) with
      | d1, None -> Delayed.return d1
      | None, d2 -> Delayed.return d2
      | _, _ -> Delayed.vanish ()
    in
    (* This is not sound, we don't take into account when, eg,
       ch1 has [i -> x] and sh2 has [i -> y], where we need to compose
       x • y and check if it's concrete. *)
    let* ch = ExpMap.sym_merge S.compose ch1 ch2 in
    let+ sh = ExpMap.sym_merge S.compose sh1 sh2 in
    (ch, sh, d)

  let is_exclusively_owned s e =
    let open Delayed.Syntax in
    match s with
    | ch, sh, Some _ ->
        let rec check l acc =
          let* acc = acc in
          match (acc, l) with
          | false, _ -> Delayed.return false
          | true, [] -> Delayed.return true
          | true, (_, hd) :: tl -> check tl (S.is_exclusively_owned hd e)
        in
        Delayed.return true
        |> check (ExpMap.bindings ch)
        |> check (ExpMap.bindings sh)
    | _, _, None -> Delayed.return false

  let is_empty = function
    | _, _, Some _ -> false
    | ch, sh, None ->
        ExpMap.for_all (fun _ s -> S.is_empty s) ch
        && ExpMap.for_all (fun _ s -> S.is_empty s) sh

  let is_concrete = function
    | _, sh, Some d -> Expr.is_concrete d && ExpMap.is_empty sh
    | _, sh, None -> ExpMap.is_empty sh

  let instantiate = function
    | [] -> ((ExpMap.empty, ExpMap.empty, Some (Expr.ESet [])), [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub (ch, sh, d) =
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
    (ch', sh', d)

  let lvars (ch, sh, d) =
    let open Containers.SS in
    let folder _ s acc = union acc (S.lvars s) in
    let lvars_map = ExpMap.fold folder ch empty in
    let lvars_map = ExpMap.fold folder sh lvars_map in
    match d with
    | None -> lvars_map
    | Some d -> union lvars_map (Expr.lvars d)

  let alocs (ch, sh, d) =
    let open Containers.SS in
    let folder _ s acc = union acc (S.alocs s) in
    let alocs_map = ExpMap.fold folder ch empty in
    let alocs_map = ExpMap.fold folder sh alocs_map in
    match d with
    | None -> alocs_map
    | Some d -> union alocs_map (Expr.alocs d)

  let lift_corepred k (p, i, o) = (SubPred p, k :: i, o)

  let assertions (ch, sh, d) =
    let folder k s acc = (List.map (lift_corepred k)) (S.assertions s) @ acc in
    let sub_assrts = ExpMap.fold folder ch [] in
    let sub_assrts = ExpMap.fold folder sh sub_assrts in
    match d with
    | None -> sub_assrts
    | Some d -> (DomainSet, [], [ d ]) :: sub_assrts

  let assertions_others (ch, sh, _) =
    List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings ch)
    @ List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings sh)

  let get_recovery_tactic = function
    | SubError (_, idx, e) ->
        Gillian.General.Recovery_tactic.merge (S.get_recovery_tactic e)
          (Gillian.General.Recovery_tactic.try_unfold [ idx ])
    | NotAllocated idx | InvalidIndexValue idx ->
        Gillian.General.Recovery_tactic.try_unfold [ idx ]
    | _ -> Gillian.General.Recovery_tactic.none

  let can_fix = function
    | SubError (_, _, e) -> S.can_fix e
    | MissingDomainSet -> true
    | AllocDisallowedInDynamic -> false
    | DomainSetNotFullyOwned -> false
    | InvalidIndexValue _ -> false
    | NotAllocated _ -> false

  let get_fixes = function
    | SubError (idx, idx', e) ->
        let open Formula.Infix in
        S.get_fixes e
        |> MyUtils.deep_map (MyAsrt.map_cp (lift_corepred idx'))
        |> List.map (fun f -> f @ [ MyAsrt.Pure idx #== idx' ])
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

module Make (I : PMapIndex) (S : MyMonadicSMemory.S) :
  PMap.PMapType
    with type entry = S.t
     and type t = S.t MyUtils.ExpMap.t * S.t MyUtils.ExpMap.t * Expr.t option =
  Make_ (I) (S) (MyUtils.ExpMap)

module MakeEnt (I : PMapIndex) (S : MyMonadicSMemory.S) :
  PMap.PMapType
    with type entry = S.t
     and type t =
      S.t MyUtils.ExpMapEnt.t * S.t MyUtils.ExpMapEnt.t * Expr.t option =
  Make_ (I) (S) (MyUtils.ExpMapEnt)
