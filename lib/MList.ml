open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
open SymResult
module DSR = DelayedSymResult
open MyUtils

(**
List state model transformer. ALlows storing a list of symbolic states, indexed by an integer in
the range \[0, n) where n is the length of the list.
Unlike PMap, there is no simplification of entries via a domainset, and instead an optional
length is used.
*)
module Make (S : MyMonadicSMemory.S) : MyMonadicSMemory.S = struct
  type t = S.t ExpMap.t * Expr.t option [@@deriving yojson]

  let pp fmt ((b, n) : t) =
    Format.fprintf fmt "{ %a }, %a" (ExpMap.make_pp S.pp) b (pp_opt Expr.pp) n

  let show s = Format.asprintf "%a" pp s

  type c_fix_t = SubFix of Expr.t * S.c_fix_t [@@deriving show]

  type err_t =
    | OutOfBounds of Expr.t * Expr.t (* Accessed index, list length *)
    | SubError of Expr.t * S.err_t
  [@@deriving show, yojson]

  type miss_t =
    | MissingCell of Expr.t (* Accessed index *)
    | MissingLength
    | SubMiss of Expr.t * S.miss_t
  [@@deriving show, yojson]

  type action = S.action

  let action_from_str = S.action_from_str
  let action_to_str = S.action_to_str

  let list_actions () =
    List.map
      (fun (a, args, ret) -> (a, "offset" :: args, ret))
      (S.list_actions ())

  type pred = Length | SubPred of S.pred

  let pred_from_str = function
    | "length" -> Some Length
    | str -> Option.map (fun p -> SubPred p) (S.pred_from_str str)

  let pred_to_str = function
    | Length -> "length"
    | SubPred p -> S.pred_to_str p

  let list_preds () =
    (Length, [], [ "length" ])
    :: List.map
         (fun (p, args, ret) -> (SubPred p, "offset" :: args, ret))
         (S.list_preds ())

  let empty () : t = (ExpMap.empty, None)

  let validate_index (_, n) idx =
    let open Delayed.Syntax in
    let* idx = Delayed.reduce idx in
    match n with
    | Some n ->
        if%sat Formula.Infix.(Expr.zero_i #<= idx #&& (idx #< n)) then DSR.ok ()
        else DSR.lfail (OutOfBounds (idx, n))
    | None -> DSR.ok ()

  let execute_action action ((b, n) : t) (args : Values.t list) :
      (t * Values.t list, err_t, miss_t) DSR.t =
    let open DSR.Syntax in
    let open Delayed.Syntax in
    match args with
    | idx :: args -> (
        let** () = validate_index (b, n) idx in
        let** idx, s = ExpMap.sym_find_res idx b ~miss:(MissingCell idx) in
        let+ r = S.execute_action action s args in
        match r with
        | Ok (s', v) -> Ok ((ExpMap.add idx s' b, n), v)
        | LFail e -> LFail (SubError (idx, e))
        | Miss m -> Miss (SubMiss (idx, m)))
    | [] -> failwith "Missing index for sub-action"

  let consume pred (b, n) ins =
    let open DSR.Syntax in
    let open Delayed.Syntax in
    match (pred, ins) with
    | SubPred p, idx :: ins -> (
        let** () = validate_index (b, n) idx in
        let** idx, s = ExpMap.sym_find_res idx b ~miss:(MissingCell idx) in
        let+ r = S.consume p s ins in
        match r with
        | Ok (s', outs) ->
            (* TODO: this smells fishy af, bc we sometimes remove it? but not always?
               but then get a missing if entry not found?
               Need to check how to distinguish missing entry from empty? *)
            if S.is_empty s' then Ok ((ExpMap.remove idx b, n), outs)
            else Ok ((ExpMap.add idx s' b, n), outs)
        | LFail e -> LFail (SubError (idx, e))
        | Miss m -> Miss (SubMiss (idx, m)))
    | SubPred _, [] -> failwith "Missing index for sub-predicate consume"
    | Length, [] -> (
        match n with
        | Some n -> DSR.ok ((b, None), [ n ])
        | None -> DSR.miss MissingLength)
    | Length, _ -> failwith "Invalid arguments for length consume"

  let produce pred (b, n) args =
    let open Delayed.Syntax in
    let open DSR.Syntax in
    match (pred, args) with
    | SubPred p, idx :: args ->
        let*? _ = validate_index (b, n) idx in
        let* idx, s = ExpMap.sym_find_default idx b ~default:S.empty in
        let+ s' = S.produce p s args in
        (ExpMap.add idx s' b, n)
    | SubPred _, [] -> failwith "Missing index for sub-predicate produce"
    | Length, [ n' ] -> (
        match n with
        | Some _ -> Delayed.vanish ()
        | None -> Delayed.return (b, Some n'))
    | Length, _ -> failwith "Invalid arguments for length produce"

  let compose _ _ = failwith "Not implemented"

  let is_fully_owned =
    let open Formula.Infix in
    function
    | b, Some _ ->
        ExpMap.fold (fun _ v acc -> acc #&& (S.is_fully_owned v)) b Formula.True
    | _, None -> Formula.False

  let is_empty = function
    | b, Some _ -> ExpMap.fold (fun _ v acc -> acc && S.is_empty v) b true
    | _, None -> true

  let instantiate = function
    | n :: args ->
        let length =
          match n with
          | Expr.Lit (Int n) -> Z.to_int n
          | _ -> failwith "Invalid length for list instantiation"
        in
        let rec aux acc i =
          if i = length then acc
          else aux (ExpMap.add (Expr.int i) (S.instantiate args) acc) (i + 1)
        in
        let b = aux ExpMap.empty 0 in
        (b, Some n)
    | [] -> failwith "Invalid arguments for list instantiation"

  let substitution_in_place sub (b, n) =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub idx ~partial:true in
      (idx', s')
    in
    let map_entries = ExpMap.bindings b in
    let* sub_entries = Delayed.all (List.map mapper map_entries) in
    let+ b' = ExpMap.sym_compose S.compose sub_entries ExpMap.empty in
    let n' = Option.map (Subst.subst_in_expr sub ~partial:true) n in
    (b', n')

  let lvars (b, n) =
    let open Containers.SS in
    let lvars_map =
      ExpMap.fold
        (fun k v acc -> union (union (Expr.lvars k) (S.lvars v)) acc)
        b empty
    in
    match n with
    | Some n -> union lvars_map (Expr.lvars n)
    | None -> lvars_map

  let alocs (b, n) =
    let open Containers.SS in
    let alocs_map =
      ExpMap.fold
        (fun k v acc -> union (union (Expr.alocs k) (S.alocs v)) acc)
        b empty
    in
    match n with
    | Some n -> union alocs_map (Expr.alocs n)
    | None -> alocs_map

  let assertions (b, n) =
    let mapper k (p, i, o) = (SubPred p, k :: i, o) in
    let sub_asrts =
      ExpMap.fold
        (fun k v acc -> acc @ List.map (mapper k) (S.assertions v))
        b []
    in
    match n with
    | Some n -> (Length, [], [ n ]) :: sub_asrts
    | None -> sub_asrts

  let get_recovery_tactic (b, _) = function
    | SubMiss (idx, m) -> (
        match ExpMap.find_opt idx b with
        | Some s -> S.get_recovery_tactic s m
        | None -> failwith "Invalid index in get_recovery_tactic")
    | _ -> Gillian.General.Recovery_tactic.none

  let get_fixes (b, _) pfs tenv = function
    | SubMiss (idx, m) ->
        let v = ExpMap.find idx b in
        let mapper (fs, fml, t, c) =
          (List.map (fun f -> SubFix (idx, f)) fs, fml, t, c)
        in
        List.map mapper (S.get_fixes v pfs tenv m)
    | _ -> failwith "Invalid error in get_fixes"

  let apply_fix (b, n) = function
    | SubFix (idx, f) -> (
        let open Delayed.Syntax in
        let s = ExpMap.find idx b in
        let+ r = S.apply_fix s f in
        match r with
        | Ok s' -> Ok (ExpMap.add idx s' b, n)
        | LFail e -> LFail (SubError (idx, e))
        | Miss m -> Miss (SubMiss (idx, m)))
end
