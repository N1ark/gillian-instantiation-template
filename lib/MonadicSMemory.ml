open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

type init_data = unit

type vt = Values.t

type st = Subst.t

type c_fix_t = unit
type err_t = unit [@@deriving show]

type t = unit

type action_ret = (t * vt list, err_t) result

let init () = ()

let get_init_data () = ()
let clear () = ()

(* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
let execute_action ~(action_name:string) (a:t) (args:vt list) : action_ret Delayed.t =
  failwith (Printf.sprintf "Implement here (execute_action %s)" action_name)


  (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
let consume ~(core_pred:string) (a:t) (args:vt list) : action_ret Delayed.t =
  failwith (Printf.sprintf "Implement here (consume %s)" core_pred)

  (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
let produce ~(core_pred:string) (a:t) (args:vt list) : t Delayed.t =
  failwith (Printf.sprintf "Implement here (produce %s)" core_pred)



let is_overlapping_asrt _ = failwith "Implement here (is_overlapping_asrt)"

let copy () = ()

let pp _ _ = ()

let substitution_in_place _ _ = failwith "Implement here (substitution_in_place)"
let fresh_let _ = failwith "Implement here (fresh_let)"

(* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
let clean_up ?(keep=Expr.Set.empty) _ = failwith "Implement here (clean_up)"

let lvars _ = failwith "Implement here (lvars)"
let alocs _ = failwith "Implement here (alocs)"

(* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
let assertions ?(to_keep=Containers.SS.empty) _ = failwith "Implement here (assertions)"
let mem_constraints _ = failwith "Implement here (mem_constraints)"
let pp_c_fix _ _ = ()
let get_recovery_tactic _ _ = failwith "Implement here (get_recovery_tactic)"
let pp_err _ _ = ()
let get_failing_constraint _ = failwith "Implement here (get_failing_constraint)"

let get_fixes _ _ _ _ = failwith "Implement here (get_fixes)"

let can_fix _ = failwith "Implement here (can_fix)"
let apply_fix _ _ = failwith "Implement here (apply_fix)"
let pp_by_need _ _ _ = ()
let get_print_info _ _ = failwith "Implement here (get_print_info)"
let sure_is_nonempty _ = failwith "Implement here (sure_is_nonempty)"

let split_further _ _ _ _ = failwith "Implement here (split_further)"

(* TODO: deriving yojson -- I think -- should make the following not necessary to implement... *)
let err_t_to_yojson _ = failwith "Implement here (err_t_to_yojson)"
let err_t_of_yojson _ = failwith "Implement here (err_t_of_yojson)"
let to_yojson _ = failwith "Implement here (to_yojson)"
let of_yojson _ = failwith "Implement here (of_yojson)"

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
