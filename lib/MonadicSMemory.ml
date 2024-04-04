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
let execute_action = failwith "Implement here"

(* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
let consume = failwith "Implement here"
(* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
let produce = failwith "Implement here"

let is_overlapping_asrt _ = failwith "Implement here"

let copy () = ()

let pp _ _ = ()

let substitution_in_place _ _ = failwith "Implement here"
let fresh_let _ = failwith "Implement here"
(* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
let clean_up = failwith "Implement here"
let lvars _ = failwith "Implement here"
let alocs _ = failwith "Implement here"
(* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
let assertions = failwith "Implement here"
let mem_constraints _ = failwith "Implement here"
let pp_c_fix _ _ = ()
let get_recovery_tactic _ _ = failwith "Implement here"
let pp_err _ _ = ()
let get_failing_constraint _ = failwith "Implement here"

let get_fixes _ _ _ _ = failwith "Implement here"

let can_fix _ = failwith "Implement here"
let apply_fix _ _ = failwith "Implement here"
let pp_by_need _ _ _ = ()
let get_print_info _ _ = failwith "Implement here"
let sure_is_nonempty _ = failwith "Implement here"

let split_further _ _ _ _ = failwith "Implement here"

(* TODO: deriving yojson -- I think -- should make the following not necessary to implement... *)
let err_t_to_yojson _ = failwith "Implement here"
let err_t_of_yojson _ = failwith "Implement here"
let to_yojson _ = failwith "Implement here"
let of_yojson _ = failwith "Implement here"

module Lift = struct
  (* Refer to MonadicSMemory.mli *)
  let add_variables = failwith "Implement here"
end
