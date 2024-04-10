open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

open Utils

module Product
  (S1: Gillian.Monadic.MonadicSMemory.S)
  (S2: Gillian.Monadic.MonadicSMemory.S) : MonadicSMemory.S = struct

  type init_data = S1.init_data * S2.init_data

  type vt = Expr.t

  type st = Subst.t

  type c_fix_t = | F1 of S1.c_fix_t | F2 of S2.c_fix_t
  type err_t = | E1 of S1.err_t | E2 of S2.err_t
  [@@deriving show, yojson]

  type t = S1.t * S2.t
  [@@deriving show, yojson]

  type action_ret = (t * vt list, err_t) result

  let init (s1, s2) = (S1.init s1, S2.init s2)

  let get_init_data (s1, s2) = (S1.get_init_data s1, S2.get_init_data s2)
  let clear (s1, s2) = (S1.clear s1, S2.clear s2)

  (* Separate a string into a head-tail tuple *)
  let split_str s = match String.length s with
    | 0 -> None
    | _ -> Some (String.sub s 0 1, String.sub s 1 ((String.length s) - 1))

  (* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
  let execute_action ~action_name (s1, s2) args =
    let open Delayed.Syntax in
    match split_str action_name with
    | None -> failwith (Printf.sprintf "Invalid action name: %s" action_name)
    | Some ("1", action_name) ->
      let+ r1 = S1.execute_action ~action_name s1 args
      in (match r1 with
          | Ok (s1', v) -> Ok ((s1', s2), v)
          | Error e -> Error (E1 e))
    | Some ("2", action_name) ->
      let+ r2 = S2.execute_action ~action_name s2 args
      in (match r2 with
          | Ok (s2', v) -> Ok ((s1, s2'), v)
          | Error e -> Error (E2 e))
    | _ -> failwith (Printf.sprintf "Invalid action name, product actions must be prefixed with 1 or 2: %s" action_name)


  (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
  let consume ~core_pred (s1,s2) args =
    let open Delayed.Syntax in
    match split_str core_pred with
    | None -> failwith (Printf.sprintf "Invalid core predicate: %s" core_pred)
    | Some ("1", core_pred) ->
      let+ r1 = S1.consume ~core_pred s1 args
      in (match r1 with
          | Ok (s1', v) -> Ok ((s1', s2), v)
          | Error e -> Error (E1 e))
    | Some ("2", core_pred) ->
      let+ r2 = S2.consume ~core_pred s2 args
      in (match r2 with
          | Ok (s2', v) -> Ok ((s1, s2'), v)
          | Error e -> Error (E2 e))
    | _ -> failwith (Printf.sprintf "Invalid core predicate, product core predicates must be prefixed with 1 or 2: %s" core_pred)

  (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
  let produce ~core_pred (s1, s2) args =
    let open Delayed.Syntax in
    match split_str core_pred with
    | None -> failwith (Printf.sprintf "Invalid core predicate: %s" core_pred)
    | Some ("1", core_pred) ->
      let+ s1' = S1.produce ~core_pred s1 args in (s1', s2)
    | Some ("2", core_pred) ->
      let+ s2' = S2.produce ~core_pred s2 args in (s1, s2')
    | _ -> failwith (Printf.sprintf "Invalid core predicate, product core predicates must be prefixed with 1 or 2: %s" core_pred)


  let is_overlapping_asrt a = S1.is_overlapping_asrt a || S2.is_overlapping_asrt a

  let copy (s1, s2) = (S1.copy s1, S2.copy s2)

  let pp fmt (s1, s2) =
    Fmt.pf fmt "Product(%a, %a)" S1.pp s1 S2.pp s2

  let substitution_in_place st (s1, s2) =
    let open Delayed.Syntax in
    let* s1' = S1.substitution_in_place st s1 in
    let+ s2' = S2.substitution_in_place st s2 in
    (s1', s2')

  (* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
  let clean_up ?(keep=Expr.Set.empty) (s1, s2) =
    let s1_a, s1_b = S1.clean_up ~keep s1 in
    let s2_a, s2_b = S2.clean_up ~keep s2 in
    (Expr.Set.union s1_a s2_a, Expr.Set.union s1_b s2_b)

  let lvars (s1, s2) = Containers.SS.union (S1.lvars s1) (S2.lvars s2)
  let alocs (s1, s2) = Containers.SS.union (S1.alocs s1) (S2.alocs s2)

  (* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
  let assertions ?(to_keep=Containers.SS.empty) (s1, s2): Asrt.t list =
    (* Override predicates by appending 1/2, so we can then pass the predicates to the right
       part of state when consuming/producing *)
    let a1 = S1.assertions ~to_keep s1 in
    let a1 = List.map (override_preds "1") a1 in
    let a2 = S2.assertions ~to_keep s2 in
    let a2 = List.map (override_preds "2") a2 in
    a1 @ a2
  let mem_constraints (s1, s2) = S1.mem_constraints s1 @ S2.mem_constraints s2
  let pp_c_fix fmt f = match f with
    | F1 f -> Fmt.pf fmt "F1(%a)" S1.pp_c_fix f
    | F2 f -> Fmt.pf fmt "F2(%a)" S2.pp_c_fix f
  let get_recovery_tactic (s1, s2) e = match e with
    | E1 e -> S1.get_recovery_tactic s1 e
    | E2 e -> S2.get_recovery_tactic s2 e
  let pp_err fmt e = match e with
    | E1 e -> Fmt.pf fmt "E1(%a)" S1.pp_err e
    | E2 e -> Fmt.pf fmt "E2(%a)" S2.pp_err e
  let get_failing_constraint e = match e with
    | E1 e -> S1.get_failing_constraint e
    | E2 e -> S2.get_failing_constraint e

  let get_fixes (s1, s2) pfs tenv e = match e with
    | E1 e ->
      let fixes = S1.get_fixes s1 pfs tenv e in
      List.map (fun (f, fs, vs, ss) -> (List.map (fun f -> F1 f) f, fs, vs, ss)) fixes
    | E2 e ->
      let fixes = S2.get_fixes s2 pfs tenv e in
      List.map (fun (f, fs, vs, ss) -> (List.map (fun f -> F2 f) f, fs, vs, ss)) fixes

  let can_fix e = match e with
    | E1 e -> S1.can_fix e
    | E2 e -> S2.can_fix e
  let apply_fix (s1, s2) f =
    let open Delayed.Syntax in
    match f with
    | F1 f ->
      let+ s1' = S1.apply_fix s1 f in (match s1' with
      | Ok s1' -> Ok (s1', s2)
      | Error e -> Error (E1 e))
    | F2 f ->
      let+ s2' = S2.apply_fix s2 f in (match s2' with
      | Ok s2' -> Ok (s1, s2')
      | Error e -> Error (E2 e))
  let pp_by_need s fmt (s1, s2) =
    Fmt.pf fmt "Product(%a, %a)" (S1.pp_by_need s) s1 (S2.pp_by_need s) s2

  let get_print_info s (s1, s2) =
    let (s1a, s1b) = S1.get_print_info s s1 in
    let (s2a, s2b) = S2.get_print_info s s2 in
    (Containers.SS.union s1a s2a, Containers.SS.union s1b s2b)

  let sure_is_nonempty (s1, s2) = S1.sure_is_nonempty s1 && S2.sure_is_nonempty s2

  let split_further (s1, s2) pred args err  = match err with
    | E1 e -> S1.split_further s1 pred args e
    | E2 e -> S2.split_further s2 pred args e

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


end
