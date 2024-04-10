open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

type init_data = unit

type vt = Values.t

type st = Subst.t

type c_fix_t = unit
type err_t =
  | MissingState
  | DoubleAlloc
  | DoubleFree
[@@deriving show, yojson]

type t =
  | None
  | Val of Values.t
[@@deriving show, yojson]

type action_ret = (t * vt list, err_t) result


let pp_v v = Yojson.Safe.to_string (Values.to_yojson v)
let pp_t v = match v with
  | None -> "None"
  | Val v -> Printf.sprintf "Val(%s)" (pp_v v)


let init (i:init_data) : t = None
let get_init_data (i:t) : init_data = ()

let clear (v:t) : t =
  failwith "Implement here (clear)"

let execute_alloc v args = match v, args with
  | None, [v] -> Ok (Val v, [])
  | Val _, _ -> Error DoubleAlloc
  | _, _ -> failwith "Invalid alloc call"

let execute_free v args = match v, args with
  | None, _ -> Error DoubleFree
  | Val _, [] -> Ok (None, [])
  | _, _ -> failwith "Invalid free call"

let execute_load v args = match v, args with
  | None, _ -> Error MissingState
  | Val v, [] -> Ok (Val v, [v])
  | _, _ -> failwith "Invalid load call"

let execute_store v args = match v, args with
  | None, _ -> Error MissingState
  | Val v, [v'] -> Ok (Val v', [])
  | _, _ -> failwith "Invalid store call"

(* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
let execute_action ~(action_name:string) (v:t) (args:vt list) : action_ret Delayed.t =
  let res = match action_name with
    | "load" -> execute_load v args
    | "store" -> execute_store v args
    | "alloc" -> execute_alloc v args
    | "free" -> execute_free v args
    | _ -> failwith (Printf.sprintf "Unrecognized action: %s" action_name)
  in match res with
    | Ok (v', args') -> Delayed.return (Ok (v', args'))
    | Error e -> Delayed.return (Error e)

  (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
let consume ~(core_pred:string) (a:t) (args:vt list) : action_ret Delayed.t =
  failwith (Printf.sprintf "Implement here (consume %s)" core_pred)

  (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
let produce ~(core_pred:string) (a:t) (args:vt list) : t Delayed.t =
  failwith (Printf.sprintf "Implement here (produce %s)" core_pred)

let is_overlapping_asrt _ = failwith "Implement here (is_overlapping_asrt)"

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

let lvars _ = failwith "Implement here (lvars)"
let alocs _ = failwith "Implement here (alocs)"

(* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
let assertions ?(to_keep=Containers.SS.empty) _ = failwith "Implement here (assertions)"
let mem_constraints _ = failwith "Implement here (mem_constraints)"
let pp_c_fix _ _ = failwith "Implement here (pp_c_fix)"
let get_recovery_tactic _ _ = failwith "Implement here (get_recovery_tactic)"
let pp_err _ _ = failwith "Implement here (pp_err)"
let get_failing_constraint _ = failwith "Implement here (get_failing_constraint)"

let get_fixes _ _ _ _ = failwith "Implement here (get_fixes)"

let can_fix _ = failwith "Implement here (can_fix)"
let apply_fix _ _ = failwith "Implement here (apply_fix)"
let pp_by_need _ _ _ = failwith "Implement here (pp_by_need)"
let get_print_info _ _ = failwith "Implement here (get_print_info)"
let sure_is_nonempty _ = failwith "Implement here (sure_is_nonempty)"

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
