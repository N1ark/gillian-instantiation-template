open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

module Containers = Gillian.Utils.Containers
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic
module PFS = Engine.PFS

module type S = sig
  (** Type of GIL general states *)
  type t [@@deriving show, yojson]

  (** Helper types *)
  type c_fix_t [@@deriving show]
  type err_t [@@deriving show, yojson]

  (** Type of predicates and actions  *)
  type action
  type pred

  val action_from_str : string -> action option
  val pred_from_str : string -> pred option
  val pred_to_str : pred -> string

  (** Initialisation *)
  val init : unit -> t
  val clear : t -> t

  (** Execute action *)
  val execute_action : action -> t -> Values.t list -> (t * Values.t list, err_t) result Delayed.t

  (** Consume-Produce *)
  val consume : pred -> t -> Values.t list -> (t * Values.t list, err_t) result Delayed.t
  val produce : pred -> t -> Values.t list -> t Delayed.t

  (** Composition *)
  val compose : t -> t -> t

  (* For Freeable *)
  val is_fully_owned : t -> bool

  (* Core predicates: pred * ins * outs, converted to Asrt.GA *)
  val assertions : t -> (pred * Expr.t list * Expr.t list) list

  (** Helpers *)
  val lvars : t -> Containers.SS.t
  val alocs : t -> Containers.SS.t
  val substitution_in_place : Subst.t -> t -> t Delayed.t
  val get_recovery_tactic : t -> err_t -> Values.t Recovery_tactic.t

  (** Fixes *)
  val get_fixes :
    t ->
    PFS.t ->
    Type_env.t ->
    err_t ->
    (c_fix_t list * Formula.t list * (string * Type.t) list * Containers.SS.t)
    list
  val can_fix : err_t -> bool
  val apply_fix : t -> c_fix_t -> (t, err_t) result Delayed.t
end

module Defaults = struct
  (* Assume no "global context" for now *)
  type init_data = unit
  let get_init_data _ = ()

  let is_overlapping_asrt _ = false
  let copy state = state (* assumes state is immutable *)
  let get_print_info _ _ = (Containers.SS.empty, Containers.SS.empty)
  let sure_is_nonempty _ = false
  let get_failing_constraint e = failwith "Implement here (get_failing_constraint)"
  let split_further _ _ _ _ = failwith "Implement here (split_further)"
  let clean_up ?(keep=Expr.Set.empty) _ = failwith "Implement here (clean_up)"
  let mem_constraints s = []
end


module Make (Mem: S): MonadicSMemory.S with type init_data = unit = struct
  include Mem

  include Defaults

  (* Can't do much more anyways *)
  type vt = Values.t
  type st = Subst.t
  type action_ret = (t * vt list, err_t) result

  (* Wrap action / consume / produce with a nice type *)
  let execute_action ~(action_name: string) (state: t) (args: vt list): action_ret Delayed.t =
    match action_from_str action_name with
    | Some action -> execute_action action state args
    | None -> failwith ("Action not found: " ^ action_name)

  let consume ~(core_pred: string) (state: t) (args: vt list): action_ret Delayed.t =
    match pred_from_str core_pred with
    | Some pred -> consume pred state args
    | None -> failwith ("Predicate not found: " ^ core_pred)

  let produce ~(core_pred: string) (state: t) (args: vt list): t Delayed.t =
    match pred_from_str core_pred with
    | Some pred -> produce pred state args
    | None -> failwith ("Predicate not found: " ^ core_pred)

  let assertions ?to_keep s =
    let asrts = assertions s in
    List.map (fun (p, ins, outs) -> Asrt.GA (pred_to_str p, ins, outs)) asrts

  (* Override methods to keep implementations light *)
  let pp fmt s = Format.pp_print_string fmt (show s)
  let pp_err fmt e = Format.pp_print_string fmt (show_err_t e)
  let pp_c_fix fmt f = Format.pp_print_string fmt (show_c_fix_t f)
  let pp_by_need _ = pp
end
