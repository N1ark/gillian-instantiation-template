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
  val make_fresh : unit -> Expr.t

  (** The arguments used when instantiating new state. Only used in dynamic mode *)
  val default_instantiation : Expr.t list
end

module LocationIndex : PMapIndex = struct
  let mode = Static

  let make_fresh () =
    let loc = ALoc.alloc () in
    Expr.loc_from_loc_name loc

  let is_valid_index = function
    | (Expr.Lit (Loc _) | Expr.ALoc _) as l -> Delayed.return (Some l)
    | e when not (Expr.is_concrete e) -> (
        let open Delayed.Syntax in
        let* loc = Delayed.resolve_loc e in
        match loc with
        | Some l -> Delayed.return (Some (Expr.loc_from_loc_name l))
        | None ->
            let loc' = make_fresh () in
            Delayed.return ~learned:[ Formula.Infix.(loc' #== e) ] (Some loc'))
    | _ -> Delayed.return None

  let default_instantiation = []
end

module StringIndex : PMapIndex = struct
  let mode = Dynamic

  let is_valid_index = function
    | l -> Delayed.return (Some l)

  let make_fresh () = failwith "Invalid in dynamic mode"
  let default_instantiation = []
end

module Make_
    (I : PMapIndex)
    (S : MyMonadicSMemory.S)
    (ExpMap : MyUtils.SymExprMap) =
struct
  type t = S.t ExpMap.t * Expr.t option [@@deriving yojson]

  let pp fmt ((h, d) : t) =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a" (ExpMap.make_pp S.pp) h;
    Format.pp_close_box fmt ();
    match d with
    | None -> Format.fprintf fmt "@\nDomainSet: None"
    | Some d -> Format.fprintf fmt "@\nDomainSet: %a" Expr.pp d

  let show s = Format.asprintf "%a" pp s

  type c_fix_t = SubFix of Expr.t * S.c_fix_t | AddIndex of Expr.t * Expr.t
  [@@deriving show]

  type err_t =
    | MissingCell of (Expr.t * Expr.t)
    | NotAllocated of Expr.t
    | AlreadyAllocated of Expr.t
    | InvalidIndexValue of Expr.t
    | MissingDomainSet
    | AllocDisallowedInDynamic
    | SubError of Expr.t * S.err_t
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

  let modify_domain f d =
    match d with
    | None -> d
    | Some (Expr.ESet d) -> Some (Expr.ESet (f d))
    | Some _ -> failwith "Invalid index set"

  let validate_index ((h, d) : t) idx =
    let open Delayed.Syntax in
    let* idx' = I.is_valid_index idx in
    match idx' with
    | None -> DR.error (InvalidIndexValue idx)
    | Some idx' -> (
        let* match_val = ExpMap.sym_find_opt idx' h in
        match (match_val, d) with
        | Some (h', idx'', v), _ -> DR.ok (h', idx'', v)
        | None, None -> DR.error (MissingCell (idx, idx'))
        | None, Some d ->
            if%sat Formula.SetMem (idx', d) then
              DR.error (MissingCell (idx, idx'))
            else DR.error (NotAllocated idx'))

  let update_entry (h, d) idx s =
    if S.is_empty s then (ExpMap.remove idx h, d) else (ExpMap.add idx s h, d)

  let execute_action action ((h, d) : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args -> (
        let* r = validate_index (h, d) idx in
        let** (h, d), idx, s =
          match (r, I.mode) with
          | Ok (h', idx, s), _ -> DR.ok ((h', d), idx, s)
          (* In Dynamic mode, missing cells are instantiated to a default value *)
          | Error (NotAllocated idx), Dynamic
          | Error (MissingCell (_, idx)), Dynamic ->
              let s, _ = S.instantiate I.default_instantiation in
              let h' = ExpMap.add idx s h in
              let d' = modify_domain (fun d -> idx :: d) d in
              DR.ok ((h', d'), idx, s)
          | Error e, _ -> DR.error e
        in
        let+ r = S.execute_action action s args in
        match r with
        | Ok (s', v) -> Ok (update_entry (h, d) idx s', v)
        | Error e -> Error (SubError (idx, e)))
    | Alloc, args ->
        if I.mode = Dynamic then DR.error AllocDisallowedInDynamic
        else
          let idx = I.make_fresh () in
          let s, v = S.instantiate args in
          let h' = ExpMap.add idx s h in
          let d' = modify_domain (fun d -> idx :: d) d in
          DR.ok ((h', d'), idx :: v)
    | GetDomainSet, [] -> (
        match d with
        (* Implementation taken from JSIL:
           - ensure domain set is there
           - ensure the domain set is exactly the set of keys in the map
           - filter keys to remove empty cells (for JS: Nono)
           - return as a list *)
        | Some d ->
            let keys = List.map fst (ExpMap.bindings h) in
            if%ent Formula.Infix.(d #== (Expr.ESet keys)) then
              let _, pos = ExpMap.partition (fun _ s -> S.is_empty s) h in
              let keys = List.map fst (ExpMap.bindings pos) in
              DR.ok ((h, Some d), [ Expr.list keys ])
            else DR.error MissingDomainSet
        | None -> DR.error MissingDomainSet)
    | GetDomainSet, _ -> failwith "Invalid arguments for get_domainset"

  let consume pred (h, d) ins =
    let open Delayed.Syntax in
    match (pred, ins) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: ins -> (
        let* res = validate_index (h, d) idx in
        match (res, I.mode) with
        | Ok (h', idx, s), _ -> (
            let+ r = S.consume pred s ins in
            match r with
            | Ok (s', v) -> Ok (update_entry (h', d) idx s', v)
            | Error e -> Error (SubError (idx, e)))
        | Error (NotAllocated idx), Dynamic
        | Error (MissingCell (_, idx)), Dynamic -> (
            let s, _ = S.instantiate I.default_instantiation in
            let h' = ExpMap.add idx s h in
            let d' = modify_domain (fun d -> idx :: d) d in
            let+ r = S.consume pred s ins in
            match r with
            | Ok (s', v) -> Ok (update_entry (h', d') idx s', v)
            | Error e -> Error (SubError (idx, e)))
        | Error e, _ -> DR.error e)
    | DomainSet, [] -> (
        match d with
        | Some d -> DR.ok ((h, None), [ d ])
        | None -> DR.error MissingDomainSet)
    | DomainSet, _ -> failwith "Invalid number of ins for domainset"

  let produce pred (h, d) args =
    let open Delayed.Syntax in
    match (pred, args) with
    | SubPred _, [] -> failwith "Missing index for sub-predicate"
    | SubPred pred, idx :: args -> (
        let* r = validate_index (h, d) idx in
        match r with
        | Ok (h', idx, s) ->
            let+ s' = S.produce pred s args in
            update_entry (h', d) idx s'
        | Error (MissingCell (_, idx)) ->
            let s = S.empty () in
            let+ s' = S.produce pred s args in
            update_entry (h, d) idx s'
        | Error _ ->
            Logging.normal (fun m ->
                m "Warning PMap: vanishing due to invalid index");
            Delayed.vanish ())
    | DomainSet, [ d' ] -> (
        match d with
        | Some _ ->
            Logging.normal (fun m ->
                m "Warning PMap: vanishing due to duplicate domain set");
            Delayed.vanish ()
        | None -> Delayed.return (h, Some d') (* TODO: if%sat typeof set ?? *))
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

  let is_fully_owned s e =
    let open Formula.Infix in
    match s with
    | h, Some _ ->
        ExpMap.fold
          (fun _ s acc -> acc #&& (S.is_fully_owned s e))
          h Formula.True
    | _, None -> Formula.False

  let is_empty = function
    | _, Some _ -> false
    | h, None -> ExpMap.for_all (fun _ s -> S.is_empty s) h

  let instantiate = function
    | [] -> ((ExpMap.empty, Some (Expr.ESet [])), [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place sub (h, d) =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub idx ~partial:true in
      (idx', s')
    in
    let map_entries = ExpMap.bindings h in
    let* sub_entries = Delayed.all (List.map mapper map_entries) in
    let+ h' = ExpMap.sym_compose S.compose sub_entries ExpMap.empty in
    (h', d)

  let lvars (h, d) =
    let open Containers.SS in
    let lvars_map =
      ExpMap.fold (fun _ s acc -> union acc (S.lvars s)) h empty
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

  let assertions (h, d) =
    let pred_wrap k (p, i, o) = (SubPred p, k :: i, o) in
    let folder k s acc = (List.map (pred_wrap k)) (S.assertions s) @ acc in
    let sub_assrts = ExpMap.fold folder h [] in
    match d with
    | None -> sub_assrts
    | Some d -> (DomainSet, [], [ d ]) :: sub_assrts

  let assertions_others (h, _) =
    List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings h)

  let get_recovery_tactic (h, _) = function
    | SubError (idx, e) -> S.get_recovery_tactic (ExpMap.find idx h) e
    | _ -> Gillian.General.Recovery_tactic.none

  let can_fix = function
    | SubError (_, e) -> S.can_fix e
    | MissingCell _ -> true
    | _ -> false (* TODO *)

  let get_fixes (h, _) =
    let open Delayed.Syntax in
    function
    | SubError (idx, e) ->
        let+ fixes = S.get_fixes (ExpMap.find idx h) e in
        List.map (fun f -> SubFix (idx, f)) fixes
    | MissingCell (v, l) -> Delayed.return [ AddIndex (v, l) ]
    | _ -> failwith "PMap: implement get_fixes"

  let apply_fix (h, d) f =
    let open Delayed.Syntax in
    let open Formula.Infix in
    match f with
    | SubFix (idx, f) -> (
        let s = ExpMap.find idx h in
        let+ r = S.apply_fix s f in
        match r with
        | Ok s' -> Ok (ExpMap.add idx s' h, d)
        | Error e -> Error (SubError (idx, e)))
    | AddIndex (v, loc) ->
        let s = S.empty () in
        let h' = ExpMap.add loc s h in
        let d' = modify_domain (fun d -> loc :: d) d in
        DR.ok ~learned:[ v #== loc ] (h', d')
end

module Make (I : PMapIndex) (S : MyMonadicSMemory.S) =
  Make_ (I) (S) (MyUtils.ExpMap)

module MakeEnt (I : PMapIndex) (S : MyMonadicSMemory.S) :
  MyMonadicSMemory.S with type t = S.t MyUtils.ExpMapEnt.t * Expr.t option =
  Make_ (I) (S) (MyUtils.ExpMapEnt)
