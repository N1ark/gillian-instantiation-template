open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module Containers = Gillian.Utils.Containers

open Utils

module Product
  (S1: MyMonadicSMemory.S)
  (S2: MyMonadicSMemory.S) : MyMonadicSMemory.S = struct

  type t = S1.t * S2.t
  [@@deriving show, yojson]

  type action = | A1 of S1.action | A2 of S2.action
  let action_from_str s = Option.bind (split_str s) (function
    | "1", s -> Option.map (fun a -> A1 a) (S1.action_from_str s)
    | "2", s -> Option.map (fun a -> A2 a) (S2.action_from_str s)
    | _ -> None)

  type pred = | P1 of S1.pred | P2 of S2.pred
  let pred_from_str s = Option.bind (split_str s) (function
    | "1", s -> Option.map (fun p -> P1 p) (S1.pred_from_str s)
    | "2", s -> Option.map (fun p -> P2 p) (S2.pred_from_str s)
    | _ -> None)

  type c_fix_t = | F1 of S1.c_fix_t | F2 of S2.c_fix_t
  [@@deriving show]
  type err_t = | E1 of S1.err_t | E2 of S2.err_t
  [@@deriving show, yojson]

  let init (): t = (S1.init (), S2.init ())

  let clear (s1, s2) = (S1.clear s1, S2.clear s2)

  let execute_action action (s1, s2) args =
    let open Delayed.Syntax in
    match action with
    | A1 action ->
      let+ r1 = S1.execute_action action s1 args
      in (match r1 with
          | Ok (s1', v) -> Ok ((s1', s2), v)
          | Error e -> Error (E1 e))
    | A2 action ->
      let+ r2 = S2.execute_action action s2 args
      in (match r2 with
          | Ok (s2', v) -> Ok ((s1, s2'), v)
          | Error e -> Error (E2 e))

  let consume pred (s1,s2) args =
    let open Delayed.Syntax in
    match pred with
    | P1 pred ->
      let+ r1 = S1.consume pred s1 args
      in (match r1 with
          | Ok (s1', v) -> Ok ((s1', s2), v)
          | Error e -> Error (E1 e))
    | P2 pred ->
      let+ r2 = S2.consume pred s2 args
      in (match r2 with
          | Ok (s2', v) -> Ok ((s1, s2'), v)
          | Error e -> Error (E2 e))

  let produce pred (s1, s2) args =
    let open Delayed.Syntax in
    match pred with
    | P1 pred ->
      let+ s1' = S1.produce pred s1 args in (s1', s2)
    | P2 pred ->
      let+ s2' = S2.produce pred s2 args in (s1, s2')


  let compose s1 s2 = failwith "Not implemented"

  let substitution_in_place st (s1, s2) =
    let open Delayed.Syntax in
    let* s1' = S1.substitution_in_place st s1 in
    let+ s2' = S2.substitution_in_place st s2 in
    (s1', s2')

  let lvars (s1, s2) = Containers.SS.union (S1.lvars s1) (S2.lvars s2)
  let alocs (s1, s2) = Containers.SS.union (S1.alocs s1) (S2.alocs s2)

  let assertions (s1, s2): Asrt.t list =
    (* Override predicates by appending 1/2, so we can then pass the predicates to the right
       part of state when consuming/producing *)
    let a1 = S1.assertions s1 in
    let a1 = List.map (override_preds "1") a1 in
    let a2 = S2.assertions s2 in
    let a2 = List.map (override_preds "2") a2 in
    a1 @ a2

  let get_recovery_tactic (s1, s2) e = match e with
    | E1 e -> S1.get_recovery_tactic s1 e
    | E2 e -> S2.get_recovery_tactic s2 e

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
end
