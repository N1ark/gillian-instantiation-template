open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type t = Expr.t option [@@deriving show, yojson]
type err_t = MissingState [@@deriving show, yojson]
type action = Load | Store
type pred = PointsTo

let pp = Fmt.(option ~none:(any "None") Expr.pp)

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
let init _ = ()
let empty () : t = None

let execute_action action s args =
  match (action, s, args) with
  | _, None, _ -> DR.error MissingState
  | Load, Some v, [] -> DR.ok (Some v, [ v ])
  | Store, Some _, [ v' ] -> DR.ok (Some v', [])
  | a, _, args ->
      failwith
        (Fmt.str "Invalid action %s with state %a and args %a" (action_to_str a)
           pp s (Fmt.Dump.list Expr.pp) args)

let consume core_pred s args =
  match (core_pred, s, args) with
  | PointsTo, Some v, [] -> DR.ok (None, [ v ])
  | PointsTo, None, _ -> DR.error MissingState
  | PointsTo, _, _ -> failwith "Invalid PointsTo consume"

let produce core_pred s args =
  match (core_pred, s, args) with
  | PointsTo, None, [ v ] -> Delayed.return (Some v)
  | PointsTo, Some _, _ -> Delayed.vanish ()
  | PointsTo, _, _ -> failwith "Invalid PointsTo produce"

let substitution_in_place subst (heap : t) =
  match heap with
  | None -> Delayed.return None
  | Some v ->
      let v' = Subst.subst_in_expr ~partial:true subst v in
      Delayed.return (Some v')

let compose s1 s2 =
  match (s1, s2) with
  | None, s | s, None -> Delayed.return s
  | _ -> Delayed.vanish ()

let is_fully_owned s _ =
  match s with
  | None -> Delayed.return false
  | Some _ -> Delayed.return true

let is_empty = function
  | None -> true
  | Some _ -> false

let is_concrete = function
  | None -> false
  | Some v -> Expr.is_concrete v

let instantiate = function
  | [] -> (Some (Expr.Lit Undefined), [])
  | [ v ] -> (Some v, []) (* maybe we don't want two options *)
  | _ -> failwith "Invalid Excl instantiation"

let lvars = function
  | None -> Containers.SS.empty
  | Some v -> Expr.lvars v

let alocs = function
  | None -> Containers.SS.empty
  | Some v -> Expr.alocs v

let assertions = function
  | None -> []
  | Some v -> [ (PointsTo, [], [ v ]) ]

let assertions_others _ = []

let get_recovery_tactic (_ : t) (e : err_t) : Values.t Recovery_tactic.t =
  match e with
  (* | MissingState -> Recovery_tactic.try_unfold ??? *)
  | _ -> Recovery_tactic.none

let can_fix = function
  | MissingState -> true

let get_fixes = function
  | MissingState ->
      [
        [ MyAsrt.CorePred (PointsTo, [], [ LVar (Generators.fresh_svar ()) ]) ];
      ]
