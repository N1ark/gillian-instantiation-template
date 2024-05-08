open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type t = Expr.t [@@deriving show, yojson]
type c_fix_t = FAddState of Values.t [@@deriving show]
type err_t = MissingState [@@deriving show, yojson]
type action = Load | Store
type pred = PointsTo

let action_from_str = function
  | "load" -> Some Load
  | "store" -> Some Store
  | _ -> None

let action_to_str = function
  | Load -> "load"
  | Store -> "store"

let list_actions () = [ (Load, [], [ "value" ]); (Store, [ "value" ], []) ]

let pred_from_str = function
  | "points_to" -> Some PointsTo
  | _ -> None

let pred_to_str = function
  | PointsTo -> "points_to"

let list_preds () = [ (PointsTo, [], [ "value" ]) ]

let execute_action action s args =
  match (action, s, args) with
  | Load, None, _ -> DR.error MissingState
  | Load, Some v, [] -> DR.ok (Some v, [ v ])
  | Load, _, _ -> failwith "Invalid Load action"
  | Store, None, _ -> DR.error MissingState
  | Store, Some v, [ v' ] -> DR.ok (Some v', [])
  | Store, _, _ -> failwith "Invalid Store action"

let consume core_pred s args =
  match (core_pred, args) with
  | PointsTo, [] -> DR.ok (None, [ s ])
  | PointsTo, _ -> failwith "Invalid PointsTo consume"

let produce core_pred s args =
  match (core_pred, s, args) with
  | PointsTo, None, [ v ] -> Delayed.return v
  | PointsTo, Some _, _ -> Delayed.vanish ()
  | PointsTo, _, _ -> failwith "Invalid PointsTo produce"

let substitution_in_place subst s =
  Delayed.return (Subst.subst_in_expr ~partial:true subst s)

(** Composition is never defined for Exc! Lifted state model handles "empty" *)
let compose s1 s2 = Delayed.vanish ()

let is_fully_owned _ = true
let is_empty _ = false

let instantiate = function
  | [] -> Expr.int 0
  | [ v ] -> v (* maybe we don't want two options *)
  | _ -> failwith "Invalid Excl instantiation"

let lvars = Expr.lvars
let alocs = Expr.alocs
let assertions v = [ (PointsTo, [], [ v ]) ]

let get_recovery_tactic (s : t) (e : err_t) : Values.t Recovery_tactic.t =
  match e with
  (* | MissingState -> Recovery_tactic.try_unfold ??? *)
  | _ -> Recovery_tactic.none

let get_fixes s pfs tenv = function
  | MissingState ->
      [
        (* TODO: ???????? *)
        ( [ FAddState (LVar (Generators.fresh_svar ())) ],
          [],
          [],
          Containers.SS.empty );
      ]

let can_fix = function
  | MissingState -> true

let apply_fix s = function
  | FAddState v -> DR.ok v
