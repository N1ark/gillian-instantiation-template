open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type t =
| None
| Val of Values.t
[@@deriving show, yojson]

type c_fix_t =
| FAddState of Values.t
[@@deriving show]

type err_t =
| MissingState
[@@deriving show, yojson]

type action = | Load | Store
type pred = | PointsTo

let action_from_str = function
| "load" -> Some Load
| "store" -> Some Store
| _ -> None

let pred_from_str = function
| "points_to" -> Some PointsTo
| _ -> None
let pred_to_str = function
| PointsTo -> "points_to"

let init () = None
let clear (v:t) : t = None

let execute_action action s args =
  match action, s, args with
  | Load, None, _ -> DR.error MissingState
  | Load, Val v, [] -> DR.ok (Val v, [v])
  | Load, _, _ -> failwith "Invalid Load action"
  | Store, None, _ -> DR.error MissingState
  | Store, Val v, [v'] -> DR.ok (Val v', [])
  | Store, _, _ -> failwith "Invalid Store action"

let consume core_pred s args =
  match core_pred, s, args with
  | PointsTo, Val v, [] -> DR.ok (None, [v])
  | PointsTo, None, _ -> DR.error MissingState
  | PointsTo, _, _ -> failwith "Invalid PointsTo consume"

let produce core_pred s args =
  match core_pred, s, args with
  | PointsTo, None, [v] -> Delayed.return (Val v)
  | PointsTo, Val _, _ -> Delayed.vanish ()
  | PointsTo, _, _ -> failwith "Invalid PointsTo produce"

(* val substitution_in_place : st -> t -> t Delayed.t *)
let substitution_in_place subst (heap:t) =
  let open Delayed.Syntax in
  match heap with
  | None -> Delayed.return None
  | Val v -> (
      let v' = Subst.subst_in_expr ~partial:true subst v in
      Delayed.return (Val v')
    )

let compose s1 s2 = match s1, s2 with
| None, _ -> s2
| _, None -> s1
| _ -> failwith "Invalid Excl composition" (* ?? not sure *)

let is_fully_owned = function
| None -> false
| Val _ -> true

let is_empty = function
| None -> true
| Val _ -> false

let lvars s = match s with
| None -> Containers.SS.empty
| Val v -> Expr.lvars v
let alocs s = Containers.SS.empty

let assertions = function
| None -> []
| Val v -> [(PointsTo, [], [v])]

let get_recovery_tactic (s:t) (e:err_t): Values.t Recovery_tactic.t = match e with
(* | MissingState -> Recovery_tactic.try_unfold ??? *)
| _ -> Recovery_tactic.none

let get_fixes s pfs tenv = function
| MissingState -> [
  ([FAddState (LVar (Generators.fresh_svar ()))], [], [], Containers.SS.empty)
]

let can_fix = function | MissingState -> true
let apply_fix s = function | FAddState v -> DR.ok (Val v)
