open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type t = Expr.t option [@@deriving show, yojson]
type c_fix_t = FAddState of Values.t [@@deriving show]
type err_t = MissingState [@@deriving show, yojson]
type action = Load
type pred = Agree

let action_from_str = function
  | "load" -> Some Load
  | _ -> None

let action_to_str = function
  | Load -> "load"

let list_actions () = [ (Load, [], [ "value" ]) ]

let pred_from_str = function
  | "agree" -> Some Agree
  | _ -> None

let pred_to_str = function
  | Agree -> "agree"

let list_preds () = [ (Agree, [], [ "value" ]) ]
let empty () : t = None

let execute_action action s args =
  match (action, s, args) with
  | Load, None, _ -> DR.error MissingState
  | Load, Some v, [] -> DR.ok (Some v, [ v ])
  | Load, _, _ -> failwith "Invalid Load action"

let consume core_pred s args =
  match (core_pred, s, args) with
  | Agree, Some v, [] -> DR.ok (Some v, [ v ])
  | Agree, None, _ -> DR.error MissingState
  | Agree, _, _ -> failwith "Invalid Agree consume"

let produce core_pred s args =
  let open Formula.Infix in
  match (core_pred, s, args) with
  | Agree, None, [ v' ] -> Delayed.return (Some v')
  | Agree, Some v, [ v' ] -> Delayed.return ~learned:[ v #== v' ] (Some v)
  | Agree, _, _ -> failwith "Invalid PointsTo produce"

let substitution_in_place subst (heap : t) =
  let open Delayed.Syntax in
  match heap with
  | None -> Delayed.return None
  | Some v ->
      let v' = Subst.subst_in_expr ~partial:true subst v in
      Delayed.return (Some v')

let compose s1 s2 =
  let open Formula.Infix in
  match (s1, s2) with
  | None, _ -> Delayed.return s2
  | _, None -> Delayed.return s1
  | Some v1, Some v2 -> Delayed.return ~learned:[ v1 #== v2 ] (Some v1)

let is_fully_owned _ = Formula.False

let is_empty = function
  | None -> true
  | Some _ -> false

let instantiate = function
  | [] -> Some (Expr.int 0)
  | _ -> failwith "Invalid Excl instantiation"

let lvars = function
  | None -> Containers.SS.empty
  | Some v -> Expr.lvars v

let alocs = function
  | None -> Containers.SS.empty
  | Some v -> Expr.alocs v

let assertions = function
  | None -> []
  | Some v -> [ (Agree, [], [ v ]) ]

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
