open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module Containers = Gillian.Utils.Containers
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic
module PFS = Engine.PFS
open SymResult

module type S = sig
  (* Type of GIL general states *)
  type t [@@deriving show, yojson]

  (* Helper types *)
  type c_fix_t [@@deriving show]
  type err_t [@@deriving show, yojson]
  type miss_t [@@deriving show, yojson]

  (* Type of predicates and actions  *)
  type action
  type pred

  val action_from_str : string -> action option
  val action_to_str : action -> string (* only needed for debug *)
  val pred_from_str : string -> pred option
  val pred_to_str : pred -> string

  (* Initialisation *)
  val empty : unit -> t

  (* Execute action *)
  val execute_action :
    action ->
    t ->
    Values.t list ->
    (t * Values.t list, err_t, miss_t) sym_result Delayed.t

  (* Consume-Produce *)
  val consume :
    pred ->
    t ->
    Values.t list ->
    (t * Values.t list, err_t, miss_t) sym_result Delayed.t

  val produce : pred -> t -> Values.t list -> t Delayed.t

  (* Composition *)
  val compose : t -> t -> t Delayed.t

  (* For Freeable *)
  val is_fully_owned : t -> Formula.t

  (* For PMap *)
  val is_empty : t -> bool
  val instantiate : Expr.t list -> t

  (* Core predicates: pred * ins * outs, converted to Asrt.GA *)
  val assertions : t -> (pred * Expr.t list * Expr.t list) list

  (* Helpers *)
  val lvars : t -> Containers.SS.t
  val alocs : t -> Containers.SS.t
  val substitution_in_place : Subst.t -> t -> t Delayed.t

  (* Debug *)

  (** Return all available (action * arguments * outputs) *)
  val list_actions : unit -> (action * string list * string list) list

  (** Return all available (predicates * ins * outs) *)
  val list_preds : unit -> (pred * string list * string list) list

  (* Fixes *)
  val get_fixes :
    (* TODO: see if the signature can be improved... *)
    t ->
    PFS.t ->
    Type_env.t ->
    miss_t ->
    (c_fix_t list * Formula.t list * (string * Type.t) list * Containers.SS.t)
    list

  val apply_fix : t -> c_fix_t -> (t, err_t, miss_t) sym_result Delayed.t
  val get_recovery_tactic : t -> miss_t -> Values.t Recovery_tactic.t
end

module Defaults = struct
  (* Assume no "global context" for now *)
  type init_data = unit

  let get_init_data _ = ()
  let is_overlapping_asrt _ = false
  let copy state = state (* assumes state is immutable *)
  let get_print_info _ _ = (Containers.SS.empty, Containers.SS.empty)
  let sure_is_nonempty _ = false

  let get_failing_constraint _ =
    failwith "Implement here (get_failing_constraint)"

  let split_further _ _ _ _ = failwith "Implement here (split_further)"

  let clean_up ?keep:(_ = Expr.Set.empty) _ =
    failwith "Implement here (clean_up)"

  let mem_constraints _ = []
end

module Make (Mem : S) : MonadicSMemory.S with type init_data = unit = struct
  include Mem
  include Defaults

  (* Re-map error type *)
  type err_t = LFail of Mem.err_t | Miss of miss_t [@@deriving show, yojson]

  let result_map (r : ('a, Mem.err_t, miss_t) sym_result) : ('a, err_t) result =
    match r with
    | Ok x -> Ok x
    | LFail e -> Error (LFail e)
    | Miss m -> Error (Miss m)

  (* Can't do much more anyways *)
  type vt = Values.t
  type st = Subst.t
  type action_ret = (t * vt list, err_t) result

  (* Wrap action / consume / produce with a nice type *)
  let init = empty

  let execute_action ~(action_name : string) (state : t) (args : vt list) :
      action_ret Delayed.t =
    match action_from_str action_name with
    | Some action -> Delayed.map (execute_action action state args) result_map
    | None -> failwith ("Action not found: " ^ action_name)

  let consume ~(core_pred : string) (state : t) (args : vt list) :
      action_ret Delayed.t =
    match pred_from_str core_pred with
    | Some pred -> Delayed.map (consume pred state args) result_map
    | None -> failwith ("Predicate not found: " ^ core_pred)

  let produce ~(core_pred : string) (state : t) (args : vt list) : t Delayed.t =
    match pred_from_str core_pred with
    | Some pred -> produce pred state args
    | None -> failwith ("Predicate not found: " ^ core_pred)

  let assertions ?to_keep:_ s =
    let asrts = assertions s in
    List.map (fun (p, ins, outs) -> Asrt.GA (pred_to_str p, ins, outs)) asrts

  (* Fix error-related functions *)
  let get_recovery_tactic t e =
    match e with
    | Miss m -> get_recovery_tactic t m
    | _ ->
        Gillian.General.Recovery_tactic.none
        (* failwith ("get_recovery_tactic: expected Miss, got " ^ (show_err_t e))*)

  let get_fixes t pfs tenv e =
    match e with
    | Miss m -> get_fixes t pfs tenv m
    | _ -> failwith "get_fixes: expected Miss"

  let apply_fix t f : (t, err_t) result Delayed.t =
    Delayed.map (apply_fix t f) result_map

  let can_fix = function
    | LFail _ -> false
    | Miss _ -> true

  (* Override methods to keep implementations light *)
  let clear _ = empty ()
  let pp fmt s = Format.pp_print_string fmt (show s)
  let pp_err fmt e = Format.pp_print_string fmt (show_err_t e)
  let pp_c_fix fmt f = Format.pp_print_string fmt (show_c_fix_t f)
  let pp_by_need _ = pp
end
