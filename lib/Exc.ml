open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type t = Expr.t option [@@deriving show, yojson]
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
let empty () : t = None (* TODO: Should it be Val (Expr.int 0)? *)
let clear (v : t) : t = None

let execute_action action s args =
  match (action, s, args) with
  | Load, None, _ -> DR.error MissingState
  | Load, Some v, [] -> DR.ok (Some v, [ v ])
  | Load, _, _ -> failwith "Invalid Load action"
  | Store, None, _ -> DR.error MissingState
  | Store, Some v, [ v' ] -> DR.ok (Some v', [])
  | Store, _, _ -> failwith "Invalid Store action"

let consume core_pred s args =
  Logging.normal (fun m -> m "Exc consuming : %s / %s / %a" (show s) (pred_to_str core_pred) (Fmt.list Expr.pp) args);
  match (core_pred, s, args) with
  | PointsTo, Some v, [] -> DR.ok (None, [ v ])
  | PointsTo, None, _ -> DR.error MissingState
  | PointsTo, _, _ -> failwith "Invalid PointsTo consume"

let produce core_pred s args =
  Logging.normal (fun m -> m "Exc Producing : %s / %s / %a" (show s) (pred_to_str core_pred) (Fmt.list Expr.pp) args);
  match (core_pred, s, args) with
  | PointsTo, None, [ v ] -> Delayed.return (Some v)
  | PointsTo, Some _, _ ->
      Logging.normal (fun m -> m "Warning Exc: vanishing due to dup resource");
      Delayed.vanish ()
  | PointsTo, _, _ -> failwith "Invalid PointsTo produce"

let substitution_in_place subst (heap : t) =
  let open Delayed.Syntax in
  match heap with
  | None -> Delayed.return None
  | Some v ->
      let v' = Subst.subst_in_expr ~partial:true subst v in
      Delayed.return (Some v')

let compose s1 s2 =
  match (s1, s2) with
  | None, _ -> Delayed.return s2
  | _, None -> Delayed.return s1
  | _ -> Delayed.vanish ()

let is_fully_owned = function
  | None -> false
  | Some _ -> true

let is_empty = function
  | None -> true
  | Some _ -> false

let instantiate = function
  | [] -> Some (Expr.int 0)
  | [ v ] -> Some v (* maybe we don't want two options *)
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
  | FAddState v -> DR.ok (Some v)
