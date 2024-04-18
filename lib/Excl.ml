open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic

type init_data = unit

type vt = Values.t

type st = Subst.t

type c_fix_t =
  | FAddState of vt
type err_t =
  | MissingState
[@@deriving show, yojson]

type t =
  | None
  | Val of Values.t
[@@deriving show, yojson]

type action_ret = (t * vt list, err_t) result

let core_pred ?(ins=[]) ?(outs=[]) p = Asrt.GA (p, ins, outs)

let pp_v v = Yojson.Safe.to_string (Values.to_yojson v)
let pp_t v = match v with
  | None -> "None"
  | Val v -> Printf.sprintf "Val(%s)" (pp_v v)


let init (i:init_data) : t = None
let get_init_data (i:t) : init_data = ()

let clear (v:t) : t = None

(* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
let execute_action ~(action_name:string) (v:t) (args:vt list) : action_ret Delayed.t =
  match action_name, v, args with
    | "load", None, _ -> DR.error MissingState
    | "load", Val v, [] -> DR.ok (Val v, [v])
    | "store", None, _ -> DR.error MissingState
    | "store", Val v, [v'] -> DR.ok (Val v', [])
    | _ -> failwith (Printf.sprintf "Unrecognized action: %s" action_name)

  (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
let consume ~(core_pred:string) (a:t) (args:vt list) : action_ret Delayed.t =
  match core_pred, a, args with
  | "points_to", Val v, [] -> DR.ok (None, [v])
  | "points_to", None, _ -> DR.error MissingState
  | _ -> failwith (Printf.sprintf "Invalid core predicate call: %s" core_pred)

  (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
let produce ~(core_pred:string) (a:t) (args:vt list) : t Delayed.t =
  match core_pred, a, args with
  | "points_to", None, [v] -> Delayed.return (Val v)
  | "points_to", Val _, _ -> Delayed.vanish ()
  | _ -> failwith (Printf.sprintf "Unrecognized core predicate: %s" core_pred)

let is_overlapping_asrt a = false

let copy v = v

let pp fmt s = Format.fprintf fmt "%s" (pp_t s)

(* val substitution_in_place : st -> t -> t Delayed.t *)
let substitution_in_place subst (heap:t) =
  let open Delayed.Syntax in
  match heap with
  | None -> Delayed.return None
  | Val v -> (
      let v' = Subst.subst_in_expr ~partial:true subst v in
      Delayed.return (Val v')
    )

(* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
let clean_up ?(keep=Expr.Set.empty) _ = failwith "Implement here (clean_up)"

let lvars s = match s with
  | None -> Containers.SS.empty
  | Val v -> Expr.lvars v
let alocs s = Containers.SS.empty

let assertions ?(to_keep=Containers.SS.empty) s: Asrt.t list = match s with
  | None -> []
  | Val v -> [core_pred "points_to" ~outs:[v]]
let mem_constraints s = []
let pp_c_fix fmt _ = Format.fprintf fmt "fix"
let get_recovery_tactic (s:t) (e:err_t): vt Recovery_tactic.t = match e with
  (* | MissingState -> Recovery_tactic.try_unfold ??? *)
  | _ -> Recovery_tactic.none

let pp_err fmt e = Format.fprintf fmt "%s" (show_err_t e)
let get_failing_constraint e = failwith "Implement here (get_failing_constraint)"

let get_fixes s pfs tenv = function
  | MissingState -> [
    ([FAddState (LVar (Generators.fresh_svar ()))], [], [], Containers.SS.empty)
  ]

let can_fix = function | MissingState -> true
let apply_fix s = function | FAddState v -> DR.ok (Val v)
let pp_by_need _ = pp
let get_print_info _ _ = (Containers.SS.empty, Containers.SS.empty)
let sure_is_nonempty _ = false

let split_further _ _ _ _ = failwith "Implement here (split_further)"

module Lift = struct

  open Gillian.Debugger.Utils

  (* Refer to MonadicSMemory.mli *)

  let add_variables
    ~(store:(string * vt) list)
    ~(memory:t)
    ~(is_gil_file:'a)
    ~(get_new_scope_id:(unit -> int))
    (scopes:(int, Variable.t list) Hashtbl.t)
    : Variable.scope list =
    failwith "Implement here (add_variables)"

end
