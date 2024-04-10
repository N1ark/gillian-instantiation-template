open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

module Sum
  (S1: Gillian.Monadic.MonadicSMemory.S)
  (S2: Gillian.Monadic.MonadicSMemory.S) : MonadicSMemory.S = struct

  type init_data = | I1 of S1.init_data | I2 of S2.init_data

  type vt = Expr.t

  type st = Subst.t

  type c_fix_t = | F1 of S1.c_fix_t | F2 of S2.c_fix_t
  type err_t = | E1 of S1.err_t | E2 of S2.err_t
  [@@deriving show, yojson]

  type t = | S1 of S1.t | S2 of S2.t
  [@@deriving show, yojson]

  type action_ret = (t * vt list, err_t) result

  let split_state f1 f2 s =
    match s with
    | S1 s1 -> f1 s1
    | S2 s2 -> f2 s2

  let split_err f1 f2 e =
    match e with
    | E1 e1 -> f1 e1
    | E2 e2 -> f2 e2

  let init i = match i with
    | I1 i -> S1 (S1.init i)
    | I2 i -> S2 (S2.init i)

  let get_init_data (s:t): init_data = match s with
    | S1 s1 -> I1 (S1.get_init_data s1)
    | S2 s2 -> I2 (S2.get_init_data s2)

  let clear s = match s with
    | S1 s1 -> S1 (S1.clear s1)
    | S2 s2 -> S2 (S2.clear s2)

  (* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
  let execute_action ~action_name a args =
    let open Delayed.Syntax in
    match a with
    | S1 a1 ->
      let+ res = S1.execute_action ~action_name a1 args in (match res with
      | Ok (a1', args') -> Ok (S1 a1', args')
      | Error e -> Error (E1 e))
    | S2 a2 ->
      let+ res = S2.execute_action ~action_name a2 args in (match res with
      | Ok (a2', args') -> Ok (S2 a2', args')
      | Error e -> Error (E2 e))


    (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
  let consume ~(core_pred:string) (a:t) (args:vt list) : action_ret Delayed.t =
    let open Delayed.Syntax in
    match a with
    | S1 a1 ->
      let+ res = S1.consume ~core_pred a1 args in (match res with
      | Ok (a1', args') -> Ok (S1 a1', args')
      | Error e -> Error (E1 e))
    | S2 a2 ->
      let+ res = S2.consume ~core_pred a2 args in (match res with
      | Ok (a2', args') -> Ok (S2 a2', args')
      | Error e -> Error (E2 e))

    (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
  let produce ~(core_pred:string) (a:t) (args:vt list) : t Delayed.t =
    let open Delayed.Syntax in
    match a with
    | S1 a1 ->
      let+ a1' = S1.produce ~core_pred a1 args in S1 a1'
    | S2 a2 ->
      let+ a2' = S2.produce ~core_pred a2 args in S2 a2'


  let is_overlapping_asrt s = S1.is_overlapping_asrt s || S2.is_overlapping_asrt s

  let copy s = match s with
    | S1 s1 -> S1 (S1.copy s1)
    | S2 s2 -> S2 (S2.copy s2)

  let pp fmt s = split_state (S1.pp fmt) (S2.pp fmt) s

  let substitution_in_place st t =
    let open Delayed.Syntax in
    match t with
    | S1 t1 -> let+ t1' = S1.substitution_in_place st t1 in S1 t1'
    | S2 t2 -> let+ t2' = S2.substitution_in_place st t2 in S2 t2'

  (* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
  let clean_up ?(keep=Expr.Set.empty) = split_state (S1.clean_up ~keep) (S2.clean_up ~keep)

  let lvars = split_state S1.lvars S2.lvars
  let alocs = split_state S1.alocs S2.alocs

  (* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
  let assertions ?(to_keep=Containers.SS.empty) = split_state (S1.assertions ~to_keep) (S2.assertions ~to_keep)
  let mem_constraints = split_state S1.mem_constraints S2.mem_constraints
  let pp_c_fix fmt f = match f with
    | F1 f1 -> S1.pp_c_fix fmt f1
    | F2 f2 -> S2.pp_c_fix fmt f2
  let get_recovery_tactic s e = match s, e with
    | S1 s1, E1 e1 -> S1.get_recovery_tactic s1 e1
    | S2 s2, E2 e2 -> S2.get_recovery_tactic s2 e2
    | _ -> failwith "get_recovery_tactic: mismatched arguments"
  let pp_err fmt = split_err (S1.pp_err fmt) (S2.pp_err fmt)
  let get_failing_constraint = split_err S1.get_failing_constraint S2.get_failing_constraint

  let get_fixes s pfs tenv e =
    match s, e with
    | S1 s1, E1 e1 ->
      let fixes = S1.get_fixes s1 pfs tenv e1 in
      (List.map (fun (fxs, fml, vars, lvars) -> (List.map (fun fx -> F1 fx) fxs, fml, vars, lvars)) fixes)
    | S2 s2, E2 e2 ->
      let fixes = S2.get_fixes s2 pfs tenv e2 in
      (List.map (fun (fxs, fml, vars, lvars) -> (List.map (fun fx -> F2 fx) fxs, fml, vars, lvars)) fixes)
    | _ -> failwith "get_fixes: mismatched arguments"

  let can_fix = split_err S1.can_fix S2.can_fix
  let apply_fix s f =
    let open Delayed.Syntax in
    match s, f with
    | S1 s1, F1 f1 ->
      let+ res = (S1.apply_fix s1 f1) in (match res with
      | Ok s1' -> Ok (S1 s1')
      | Error e -> Error (E1 e))
    | S2 s2, F2 f2 ->
      let+ res = (S2.apply_fix s2 f2) in (match res with
      | Ok s2' -> Ok (S2 s2')
      | Error e -> Error (E2 e))
    | _ -> failwith "apply_fix: mismatched arguments"

  let pp_by_need c fmt = split_state (S1.pp_by_need c fmt) (S2.pp_by_need c fmt)
  let get_print_info c = split_state (S1.get_print_info c) (S2.get_print_info c)
  let sure_is_nonempty = split_state S1.sure_is_nonempty S2.sure_is_nonempty

  let split_further s core_pred args e = match s, e with
    | S1 s1, E1 e1 -> S1.split_further s1 core_pred args e1
    | S2 s2, E2 e2 -> S2.split_further s2 core_pred args e2
    | _ -> failwith "split_further: mismatched arguments"

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
      failwith "Sum.Lift.add_variables not implemented"

  end


end
