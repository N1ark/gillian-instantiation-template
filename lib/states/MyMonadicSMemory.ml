open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module Containers = Gillian.Utils.Containers
module DR = Delayed_result
module Recovery_tactic = Gillian.General.Recovery_tactic
module PFS = Engine.PFS

module type S = sig
  (* Type of GIL general states *)
  type t [@@deriving yojson]

  (* Helper types *)
  type err_t [@@deriving show, yojson]

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
    action -> t -> Values.t list -> (t * Values.t list, err_t) result Delayed.t

  (* Consume-Produce *)
  val consume :
    pred -> t -> Values.t list -> (t * Values.t list, err_t) result Delayed.t

  val produce : pred -> t -> Values.t list -> t Delayed.t

  (* Composition *)
  val compose : t -> t -> t Delayed.t

  (* For Freeable *)
  val is_fully_owned : t -> Expr.t list -> Formula.t

  (* For PMap *)
  val is_empty : t -> bool
  val is_concrete : t -> bool
  val instantiate : Expr.t list -> t * Expr.t list

  (* Core predicates: pred * ins * outs, converted to Asrt.GA *)
  val assertions : t -> (pred * Expr.t list * Expr.t list) list
  val assertions_others : t -> Asrt.t list

  (* Helpers *)
  val lvars : t -> Containers.SS.t
  val alocs : t -> Containers.SS.t
  val substitution_in_place : Subst.t -> t -> t Delayed.t
  val get_recovery_tactic : t -> err_t -> Values.t Recovery_tactic.t
  val pp : Format.formatter -> t -> unit

  (* Debug *)

  (** Return all available (action * arguments * outputs) *)
  val list_actions : unit -> (action * string list * string list) list

  (** Return all available (predicates * ins * outs) *)
  val list_preds : unit -> (pred * string list * string list) list

  (* Fixes *)
  val can_fix : err_t -> bool
  val get_fixes : err_t -> pred MyAsrt.t list list
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

  let split_further _ _ _ _ = None
  let clean_up ?(keep = Expr.Set.empty) _ = (Expr.Set.empty, keep)
  let mem_constraints _ = []
end

module Make (Mem : S) : MonadicSMemory.S with type init_data = unit = struct
  include Mem
  include Defaults

  (* Can't do much more anyways *)
  type vt = Values.t
  type st = Subst.t
  type action_ret = (t * vt list, err_t) result

  (* Wrap action / consume / produce with a nice type *)
  let init = empty

  type c_fix_t = pred * Expr.t list * Expr.t list

  let execute_action ~(action_name : string) (state : t) (args : vt list) :
      action_ret Delayed.t =
    match action_from_str action_name with
    | Some action -> execute_action action state args
    | None -> failwith ("Action not found: " ^ action_name)

  let consume ~(core_pred : string) (state : t) (args : vt list) :
      action_ret Delayed.t =
    match pred_from_str core_pred with
    | Some pred -> consume pred state args
    | None -> failwith ("Predicate not found: " ^ core_pred)

  let produce ~(core_pred : string) (state : t) (args : vt list) : t Delayed.t =
    match pred_from_str core_pred with
    | Some pred -> produce pred state args
    | None -> failwith ("Predicate not found: " ^ core_pred)

  let assertions ?to_keep:_ s =
    let core_preds = assertions s in
    let formulas = assertions_others s in
    let mapping (p, ins, outs) = Asrt.GA (pred_to_str p, ins, outs) in
    List.map mapping core_preds @ formulas

  let get_fixes _ _ _ e =
    let rec build_fixes (corepreds, fmls, types, specvars) fix =
      match fix with
      | [] -> (corepreds, fmls, types, specvars)
      | fix :: fixes ->
          build_fixes
            (match fix with
            | MyAsrt.Emp -> (corepreds, fmls, types, specvars)
            | MyAsrt.Pure fml -> (corepreds, fml :: fmls, types, specvars)
            | MyAsrt.Types ts -> (corepreds, fmls, ts @ types, specvars)
            | MyAsrt.CorePred (preds, ins, outs) ->
                ((preds, ins, outs) :: corepreds, fmls, types, specvars))
            fixes
    in
    let fixes = get_fixes e in
    List.map (build_fixes ([], [], [], Containers.SS.empty)) fixes

  let apply_fix s (pred, ins, outs) =
    Delayed.map (Mem.produce pred s (ins @ outs)) Result.ok

  (* Override methods to keep implementations light *)
  let clear _ = empty ()
  let pp_err = pp_err_t

  let pp_c_fix (fmt : Format.formatter) ((p, ins, outs) : c_fix_t) : unit =
    Format.fprintf fmt "<%s>(%a;%a)" (pred_to_str p)
      Fmt.(list ~sep:comma Expr.pp)
      ins
      Fmt.(list ~sep:comma Expr.pp)
      outs

  let pp_by_need _ = pp
end
