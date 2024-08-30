open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type t = Expr.t option [@@deriving yojson]
type err_t = MissingState [@@deriving show, yojson]
type action = Load
type pred = Agree

let pp = Fmt.(option ~none:(any "None") Expr.pp)

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
  | Agree, _, _ ->
      failwith
        (Fmt.str "Invalid Agree produce, got args [%a]"
           (Fmt.list ~sep:Fmt.comma Expr.pp)
           args)

let substitution_in_place subst (heap : t) =
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

let is_fully_owned _ _ = Delayed.return false

let is_empty = function
  | None -> true
  | Some _ -> false

let is_concrete = function
  | None -> true
  | Some v -> Expr.is_concrete v

let instantiate = function
  | [ v ] -> (Some v, [])
  | args ->
      failwith
        ("Invalid Agreement instantiation: "
        ^ Fmt.to_to_string (Fmt.list ~sep:Fmt.comma Expr.pp) args)

let lvars = function
  | None -> Containers.SS.empty
  | Some v -> Expr.lvars v

let alocs = function
  | None -> Containers.SS.empty
  | Some v -> Expr.alocs v

let assertions = function
  | None -> []
  | Some v -> [ (Agree, [], [ v ]) ]

let assertions_others _ = []

let get_recovery_tactic (e : err_t) : Values.t Recovery_tactic.t =
  match e with
  (* | MissingState -> Recovery_tactic.try_unfold ??? *)
  | _ -> Recovery_tactic.none

let can_fix = function
  | MissingState -> true

let get_fixes = function
  | MissingState ->
      [ [ MyAsrt.CorePred (Agree, [], [ LVar (Generators.fresh_svar ()) ]) ] ]
