open Gil_syntax
open Gillian.Monadic
module Subst = Gillian.Symbolic.Subst
module DR = Delayed_result
module DO = Delayed_option

module type OpenPMapImpl = sig
  type entry
  type t [@@deriving yojson]

  val pp : Format.formatter -> t -> unit
  val empty : t
  val fold : (Expr.t -> entry -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (entry -> bool) -> t -> bool

  (** Returns (symbolically) the state at the given index if it's found,
      or None if no state can be there (ie. the index is not valid, for open PMaps). *)
  val validate_index : t -> Expr.t -> (Expr.t * entry) option Delayed.t

  (** Updates the entry with the given state; `idx` represents the previous
      index of the state, in case a new index was found for it. In other words, after
      this operation the map must store nothing at `idx`, and the new state at `idx'`.
      `idx` and `idx'` can be equal, in which case the state is just added/updated. *)
  val update_entry : idx:Expr.t -> idx':Expr.t -> entry -> t -> t

  val compose : t -> t -> t Delayed.t
  val substitution_in_place : Subst.t -> t -> t Delayed.t
end

module type OpenPMapType = sig
  include MyMonadicSMemory.S

  type entry

  val validate_index : t -> Expr.t -> (Expr.t * entry, err_t) DR.t
  val update_entry : idx:Expr.t -> idx':Expr.t -> entry -> t -> t
end

module MakeOfImpl
    (I_Cons : functor
      (S : MyMonadicSMemory.S)
      -> OpenPMapImpl with type entry = S.t)
    (S : MyMonadicSMemory.S) =
struct
  module I = I_Cons (S)

  type entry = S.t
  type t = I.t [@@deriving yojson]

  let pp fmt (h : t) =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a" I.pp h;
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

  let update_entry = I.update_entry

  let validate_index s idx =
    Delayed.map (I.validate_index s idx) (function
      | None -> Error (InvalidIndexValue idx)
      | Some ss -> Ok ss)

  let lifting_err idx idx' v fn =
    match v with
    | Ok v -> Ok (fn v)
    | Error e -> Error (SubError (idx, idx', e))

  let empty () : t = I.empty

  let execute_action action (s : t) args =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match (action, args) with
    | SubAction _, [] -> failwith "Missing index for sub-action"
    | SubAction action, idx :: args ->
        let** idx', ss = validate_index s idx in
        let+ r = S.execute_action action ss args in
        let ( let+^ ) = lifting_err idx idx' in
        let+^ ss', v = r in
        let s' = update_entry ~idx ~idx' ss' s in
        (s', idx' :: v)
    | Alloc, args ->
        let idx = Expr.ALoc (ALoc.alloc ()) in
        let ss, v = S.instantiate args in
        let s' = update_entry ~idx ~idx':idx ss s in
        DR.ok (s', idx :: v)

  let consume pred s ins =
    let open Delayed.Syntax in
    let open DR.Syntax in
    match ins with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: ins ->
        let** idx', ss = validate_index s idx in
        let+ r = S.consume pred ss ins in
        let ( let+^ ) = lifting_err idx idx' in
        let+^ ss', v = r in
        let s' = update_entry ~idx ~idx' ss' s in
        (s', v)

  let produce pred s args =
    let open Delayed.Syntax in
    let open MyUtils.Syntax in
    match args with
    | [] -> failwith "Missing index for sub-predicate"
    | idx :: args ->
        let*? idx', ss = validate_index s idx in
        let+ ss' = S.produce pred ss args in
        update_entry ~idx ~idx' ss' s

  let compose = I.compose
  let is_exclusively_owned _ _ = Delayed.return false
  let is_empty = I.for_all S.is_empty
  let is_concrete = I.for_all S.is_concrete

  let instantiate = function
    | [] -> (I.empty, [])
    | _ -> failwith "Invalid arguments for instantiation"

  let substitution_in_place = I.substitution_in_place

  let accumulate ~fn_k ~fn_v h =
    let open Utils.Containers.SS in
    I.fold (fun k s acc -> fn_v s |> union @@ fn_k k |> union acc) h empty

  let lvars = accumulate ~fn_k:Expr.lvars ~fn_v:S.lvars
  let alocs = accumulate ~fn_k:Expr.alocs ~fn_v:S.alocs
  let lift_corepred k (p, i, o) = (p, k :: i, o)

  let assertions h =
    I.fold
      (fun k s acc -> List.map (lift_corepred k) (S.assertions s) @ acc)
      h []

  let assertions_others h =
    I.fold (fun _ s acc -> S.assertions_others s @ acc) h []

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
        S.get_fixes e
        |> MyUtils.deep_map @@ MyAsrt.map_cp @@ lift_corepred idx'
        |> List.map @@ List.cons @@ Formula.Infix.(MyAsrt.Pure idx #== idx')
    | _ -> failwith "Called get_fixes on unfixable error"
end

(** "Base" implementation of an open PMap, with no particular optimisation.
    Takes as modules the backing ExpMap used (%sat or %ent), and the PMapIndex used for
    validating and generating indices. Because this PMap is *open*, it is only compatible
    with static indexing, as dynamic indexing requires a domain set to be sound. *)
module MakeBaseImpl
    (ExpMap : MyUtils.SymExprMap)
    (I : PMap.PMapIndex)
    (S : MyMonadicSMemory.S) =
struct
  type entry = S.t
  type t = S.t ExpMap.t [@@deriving yojson]

  let pp fmt h =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a" (ExpMap.make_pp S.pp) h;
    Format.pp_close_box fmt ()

  let empty = ExpMap.empty
  let fold = ExpMap.fold
  let for_all f = ExpMap.for_all (fun _ v -> f v)

  let validate_index h idx =
    let open Delayed.Syntax in
    let* idx' = I.is_valid_index idx in
    match idx' with
    | None -> DO.none ()
    | Some idx' ->
        let+ match_val = ExpMap.sym_find_opt idx' h in
        Some (Option.value ~default:(idx', S.empty ()) match_val)

  let update_entry ~idx ~idx' s h =
    if S.is_empty s then ExpMap.remove idx h
    else if Expr.equal idx idx' then ExpMap.add idx s h
    else ExpMap.remove idx h |> ExpMap.add idx' s

  let compose = ExpMap.sym_merge S.compose

  let substitution_in_place sub h =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub ~partial:true idx in
      (idx', s')
    in
    let* sub_entries = ExpMap.bindings h |> List.map mapper |> Delayed.all in
    ExpMap.sym_compose S.compose sub_entries ExpMap.empty
end

module BaseImplSat = MakeBaseImpl (MyUtils.ExpMap)
module BaseImplEnt = MakeBaseImpl (MyUtils.ExpMapEnt)

(** Implementation of an open PMap with concrete/symbolic split. *)
module MakeSplitImpl
    (ExpMap : MyUtils.SymExprMap)
    (I : PMap.PMapIndex)
    (S : MyMonadicSMemory.S) =
struct
  type entry = S.t
  type t = S.t ExpMap.t * S.t ExpMap.t [@@deriving yojson]

  let pp fmt (ch, sh) =
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

  let empty = (ExpMap.empty, ExpMap.empty)

  let fold f (ch, sh) acc =
    let acc = ExpMap.fold f ch acc in
    ExpMap.fold f sh acc

  let for_all f (ch, sh) =
    ExpMap.for_all (fun _ v -> f v) ch && ExpMap.for_all (fun _ v -> f v) sh

  let validate_index (ch, sh) idx =
    let open Delayed.Syntax in
    let* idx' = I.is_valid_index idx in
    match idx' with
    | None -> DO.none ()
    | Some idx' -> (
        (* This check might not be needed if we know idx' is not concrete *)
        match ExpMap.find_opt idx' ch with
        | Some v -> DO.some (idx', v)
        | None -> (
            match ExpMap.find_opt idx' sh with
            | Some v -> DO.some (idx', v)
            | None -> (
                let merged = ExpMap.union (fun _ v1 _ -> Some v1) ch sh in
                let* match_val = ExpMap.sym_find_opt idx' merged in
                match match_val with
                | Some (idx'', v) -> DO.some (idx'', v)
                | None -> DO.some (idx', S.empty ()))))

  let update_entry ~idx ~idx' s (ch, sh) =
    (* remove from both (dont know where it was) *)
    let ch', sh' = (ExpMap.remove idx ch, ExpMap.remove idx sh) in
    if S.is_empty s then (ch', sh')
    else if Expr.is_concrete idx' && S.is_concrete s then
      (ExpMap.add idx' s ch', sh')
    else (ch', ExpMap.add idx' s sh')

  let compose (ch1, sh1) (ch2, sh2) =
    let open Delayed.Syntax in
    (* This is not sound, we don't take into account when, eg,
       ch1 has [i -> x] and sh2 has [i -> y], where we need to compose
       x • y and check if it's concrete. *)
    let* ch = ExpMap.sym_merge S.compose ch1 ch2 in
    let+ sh = ExpMap.sym_merge S.compose sh1 sh2 in
    (ch, sh)

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
end

module SplitImplSat = MakeSplitImpl (MyUtils.ExpMap)
module SplitImplEnt = MakeSplitImpl (MyUtils.ExpMapEnt)

(** Implementation of an open PMap with abstract locations. *)
module ALocImpl (S : MyMonadicSMemory.S) = struct
  module SMap = MyUtils.SMap

  type entry = S.t
  type t = S.t MyUtils.SMap.t [@@deriving yojson]

  let pp fmt h =
    Format.pp_open_vbox fmt 0;
    Format.fprintf fmt "%a"
      (MyUtils.pp_bindings ~pp_k:Fmt.string ~pp_v:S.pp SMap.iter)
      h;
    Format.pp_close_box fmt ()

  let empty = SMap.empty
  let fold f = SMap.fold (fun k v acc -> f (Expr.loc_from_loc_name k) v acc)
  let for_all f = SMap.for_all (fun _ v -> f v)

  let get_loc_fast = function
    | Expr.Lit (Loc loc) -> loc
    | Expr.ALoc loc -> loc
    | _ -> failwith "Non-trivial location given to get_loc_fast"

  let validate_index h idx =
    let open Delayed.Syntax in
    let* idx_s = MyUtils.get_loc idx in
    match idx_s with
    | Some s ->
        let idx_e = Expr.loc_from_loc_name s in
        let res = SMap.find_opt s h in
        let res = Option.value ~default:(S.empty ()) res in
        DO.some (idx_e, res)
    | None -> DO.none ()

  let update_entry ~idx ~idx':_ s h =
    let idx_s = get_loc_fast idx in
    if S.is_empty s then SMap.remove idx_s h else SMap.add idx_s s h

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
end

(* Types *)
type 'e t_base_sat = 'e MyUtils.ExpMap.t
type 'e t_base_ent = 'e MyUtils.ExpMapEnt.t
type 'e t_split_sat = 'e MyUtils.ExpMap.t * 'e MyUtils.ExpMap.t
type 'e t_split_ent = 'e MyUtils.ExpMapEnt.t * 'e MyUtils.ExpMapEnt.t
type 'e t_aloc = 'e MyUtils.SMap.t
