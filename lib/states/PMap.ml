open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

type index_mode = Static | Dynamic

(**
  Type for the domain of a PMap.
  Allows configuring it to either have static or dynamic indexing:
  - Static: indexes are created by the memory model on allocation (eg. the heap in C)
  - Dynamic: indexes are given by the user on allocation (eg. objects in JS)

  The user must provide the index on allocation in dynamic mode, and mustn't provide it in static mode.
  is_valid_index must always be implemented, while make_fresh is only needed in static mode.
*)
module type PMapIndex = sig
  val mode : index_mode

  (** If the given expression is a valid index for the map.
      Returns a possibly simplified index, and None if it's not valid.  *)
  val is_valid_index : Expr.t -> Expr.t option Delayed.t

  (** Creates a new address, for allocating new state. Only used in static mode *)
  val make_fresh : unit -> Expr.t Delayed.t

  (** The arguments used when instantiating new state. Only used in dynamic mode *)
  val default_instantiation : Expr.t list
end

module LocationIndex : PMapIndex = struct
  let mode = Static

  let make_fresh () =
    let loc = ALoc.alloc () in
    Expr.loc_from_loc_name loc |> Delayed.return

  let is_valid_index e =
    Delayed_option.map (MyUtils.get_loc e) Expr.loc_from_loc_name

  let default_instantiation = []
end

module StringIndex : PMapIndex = struct
  let mode = Dynamic

  let is_valid_index = function
    | l -> Delayed.return (Some l)

  let make_fresh () = failwith "Invalid in dynamic mode"
  let default_instantiation = []
end

module IntegerIndex : PMapIndex = struct
  open Formula.Infix
  open Expr.Infix

  let mode = Static
  let last_index = ref None

  let make_fresh () =
    let lvar = LVar.alloc () in
    let e = Expr.LVar lvar in
    let learnt =
      match !last_index with
      | None -> []
      | Some last -> [ e #== (last + Expr.int 1) ]
    in
    last_index := Some e;
    Delayed.return ~learned:learnt
      ~learned_types:[ (lvar, Type.IntType) ]
      (Expr.LVar lvar)

  let is_valid_index = function
    | l -> Delayed.return (Some l)

  let default_instantiation = []
end

module Make_
    (I : PMapIndex)
    (S : MyMonadicSMemory.S)
    (ExpMap : MyUtils.SymExprMap) =
struct
  type entry = S.t [@@deriving yojson]
  type t = entry ExpMap.t * Expr.t option [@@deriving yojson]

  let pp fmt ((h, d) : t) =
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

  let empty () : t = (ExpMap.empty, None)

  let domain_add k (h, d) =
    match d with
    | None -> (h, d)
    | Some (Expr.ESet d) -> (h, Some (Expr.ESet (k :: d)))
    | Some _ -> failwith "Invalid index set"

  let validate_index ((h, d) : t) idx =
    let open Delayed.Syntax in
    let* idx' = I.is_valid_index idx in
    match idx' with
    | None -> DR.error (InvalidIndexValue idx)
    | Some idx' -> (
        let* match_val = ExpMap.sym_find_opt idx' h in
        match (match_val, d) with
        | Some (idx'', v), _ -> DR.ok (idx'', v)
        (* If the cell is not found, it is initialised to empty. Trust the below state
           models to raise a Miss error, that will then be wrapped and taken care of.
           Otherwise we would need to raise a miss error that doesn't make sense since it can't
           really be fixed; there is no 'cell' predicate in the PMap, it relies on the sub
           states' predicates being extended with an index in-argument. *)
        | None, None -> DR.ok (idx', S.empty ())
        | None, Some d ->
            if%sat Formula.SetMem (idx', d) then DR.ok (idx', S.empty ())
            else DR.error (NotAllocated idx'))

  (*
  Uncomment to allow PMap performance measurements
  let validate_index ((h, _) as s) i =
    let open Delayed.Syntax in
    let name = if I.mode = Dynamic then "unopti" else "aloc" in
    let* () = Delayed.return () in
    let now = Unix.gettimeofday () in
    let+ r = validate_index s i in
    let later = Unix.gettimeofday () in
    let size = ExpMap.cardinal h in
    Printf.printf "validate_index: %f (%i) (%s)\n" (later -. now) size name;
    r*)

  let update_entry (h, d) idx idx' s =
    if S.is_empty s then (ExpMap.remove idx h, d)
    else if Expr.equal idx idx' then (ExpMap.add idx s h, d)
    else (ExpMap.remove idx h |> ExpMap.add idx' s, d)

  let execute_action action (s : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let* r = validate_index s idx in
        let** s, idx', ss =
          match r with
          | Ok (idx, ss) -> DR.ok (s, idx, ss)
          (* In Dynamic mode, missing cells are instantiated to a default value *)
          | Error (NotAllocated idx) when I.mode = Dynamic ->
              let ss, _ = S.instantiate I.default_instantiation in
              DR.ok (domain_add idx s, idx, ss)
          | Error e -> DR.error e
        in
        let+ r = S.execute_action action ss args in
        match r with
        | Ok (ss', v) -> Ok (update_entry s idx idx' ss', idx' :: v)
        | Error e -> Error (SubError (idx, idx', e)))
    | Alloc, args -> (
        match I.mode with
        | Dynamic -> DR.error AllocDisallowedInDynamic
        | Static ->
            let+ idx = I.make_fresh () in
            let ss, v = S.instantiate args in
            let s' = update_entry s idx idx ss |> domain_add idx in
            Ok (s', idx :: v))
    | GetDomainSet, [] -> (
        match s with
        (* Implementation taken from JSIL:
           - ensure domain set is there
           - ensure the domain set is exactly the set of keys in the map
           - filter keys to remove empty cells (for JS: Nono)
           - return as a list *)
        | h, Some d ->
            let keys = List.map fst (ExpMap.bindings h) in
            if%ent Formula.Infix.(d #== (Expr.ESet keys)) then
              let _, pos = ExpMap.partition (fun _ s -> S.is_empty s) h in
              let keys = List.map fst (ExpMap.bindings pos) in
              DR.ok (s, [ Expr.list keys ])
            else DR.error DomainSetNotFullyOwned
        | _, None -> DR.error MissingDomainSet)
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
        | h, Some d -> DR.ok ((h, None), [ d ])
        | _, None -> DR.error MissingDomainSet)
    | DomainSet, _ -> failwith "Invalid number of ins for domainset"

  let produce pred s args =
    let open Delayed.Syntax in
    let open MyUtils.Syntax in
    match (pred, args) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: args ->
        let*? idx, ss = validate_index s idx in
        let+ ss' = S.produce pred ss args in
        update_entry s idx idx ss'
    | DomainSet, [ d' ] -> (
        match s with
        | _, Some _ -> Delayed.vanish ()
        | h, None ->
            (* This would be the correct implementation, but the handling of sets is bad so
               it creates all sorts of issues (eg. matching plans)...
               let dom = ExpMap.bindings h |> List.map fst in
               let dom = Expr.ESet dom in*)
            Delayed.return (*~learned:[ Formula.SetSub (dom, d') ]*) (h, Some d')
        )
    | DomainSet, _ -> failwith "Invalid arguments for domainset produce"

  let compose (h1, d1) (h2, d2) =
    let open Delayed.Syntax in
    let* d =
      match (d1, d2) with
      | d1, None -> Delayed.return d1
      | None, d2 -> Delayed.return d2
      | _, _ -> Delayed.vanish ()
    in
    let+ h = ExpMap.sym_merge S.compose h1 h2 in
    (h, d)

  let is_exclusively_owned s e =
    let open Delayed.Syntax in
    match s with
    | h, Some _ ->
        let rec check l acc =
          let* acc = acc in
          match (acc, l) with
          | false, _ -> Delayed.return false
          | true, [] -> Delayed.return true
          | true, (_, hd) :: tl -> check tl (S.is_exclusively_owned hd e)
        in
        check (ExpMap.bindings h) (Delayed.return true)
    | _, None -> Delayed.return false

  let is_empty = function
    | _, Some _ -> false
    | h, None -> ExpMap.for_all (fun _ s -> S.is_empty s) h

  let is_concrete = function
    | h, None -> ExpMap.for_all (fun _ s -> S.is_concrete s) h
    | h, Some d ->
        Expr.is_concrete d && ExpMap.for_all (fun _ s -> S.is_concrete s) h

  let instantiate = function
    | [] -> ((ExpMap.empty, Some (Expr.ESet [])), [])
    | [ Expr.EList fields ] ->
        let ss, _ = S.instantiate [] in
        let h =
          List.fold_left (fun acc k -> ExpMap.add k ss acc) ExpMap.empty fields
        in
        let d = Expr.ESet fields in
        ((h, Some d), [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub (h, d) =
    let open Delayed.Syntax in
    let subst = Subst.subst_in_expr sub ~partial:true in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = subst idx in
      (idx', s')
    in
    let* sub_entries = ExpMap.bindings h |> List.map mapper |> Delayed.all in
    let+ h' = ExpMap.sym_compose S.compose sub_entries ExpMap.empty in
    (h', d)

  let lvars (h, d) =
    let open Containers.SS in
    let lvars_map =
      ExpMap.fold
        (fun k s acc -> S.lvars s |> union (Expr.lvars k) |> union acc)
        h empty
    in
    match d with
    | None -> lvars_map
    | Some d -> union lvars_map (Expr.lvars d)

  let alocs (h, d) =
    let open Containers.SS in
    let alocs_map =
      ExpMap.fold (fun _ s acc -> union acc (S.alocs s)) h empty
    in
    match d with
    | None -> alocs_map
    | Some d -> union alocs_map (Expr.alocs d)

  let lift_corepred k (p, i, o) = (SubPred p, k :: i, o)

  let assertions (h, d) =
    let folder k s acc = (List.map @@ lift_corepred k) (S.assertions s) @ acc in
    let sub_assrts = ExpMap.fold folder h [] in
    match d with
    | None -> sub_assrts
    | Some d -> (DomainSet, [], [ d ]) :: sub_assrts

  let assertions_others (h, _) =
    List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings h)

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
        let lvar = Expr.LVar (LVar.alloc ()) in
        [
          [
            MyAsrt.CorePred (DomainSet, [], [ lvar ]);
            MyAsrt.Types [ (lvar, Type.SetType) ];
          ];
        ]
    | _ -> failwith "Called get_fixes on unfixable error"
end

module type PMapType = sig
  include MyMonadicSMemory.S

  type entry

  val validate_index : t -> Expr.t -> (Expr.t * entry, err_t) DR.t
  val update_entry : t -> Expr.t -> Expr.t -> entry -> t
  val domain_add : Expr.t -> t -> t
end

module Make (I : PMapIndex) (S : MyMonadicSMemory.S) =
  Make_ (I) (S) (MyUtils.ExpMap)

module MakeEnt (I : PMapIndex) (S : MyMonadicSMemory.S) =
  Make_ (I) (S) (MyUtils.ExpMapEnt)
