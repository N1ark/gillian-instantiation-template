open Gillian.Monadic
open Gil_syntax
module Containers = Gillian.Utils.Containers
open MyUtils

module Make (IDs : IDs) (S1 : MyMonadicSMemory.S) (S2 : MyMonadicSMemory.S) :
  MyMonadicSMemory.S with type t = S1.t * S2.t = struct
  type t = S1.t * S2.t [@@deriving yojson]

  let pp fmt (s1, s2) =
    Fmt.pf fmt "Product (@[<v>%a@]) × (@[<v>%a@])" S1.pp s1 S2.pp s2

  let show s = Format.asprintf "%a" pp s

  module IDer = Identifier (IDs)

  type action = A1 of S1.action | A2 of S2.action

  let action_from_str s =
    match IDer.get_ided s with
    | ID1 s -> Option.map (fun a -> A1 a) (S1.action_from_str s)
    | ID2 s -> Option.map (fun a -> A2 a) (S2.action_from_str s)
    | NotIDed _ -> None

  let action_to_str = function
    | A1 a -> IDs.id1 ^ S1.action_to_str a
    | A2 a -> IDs.id2 ^ S2.action_to_str a

  let list_actions () =
    List.map (fun (a, args, ret) -> (A1 a, args, ret)) (S1.list_actions ())
    @ List.map (fun (a, args, ret) -> (A2 a, args, ret)) (S2.list_actions ())

  type pred = P1 of S1.pred | P2 of S2.pred

  let pred_from_str s =
    match IDer.get_ided s with
    | ID1 s -> Option.map (fun p -> P1 p) (S1.pred_from_str s)
    | ID2 s -> Option.map (fun p -> P2 p) (S2.pred_from_str s)
    | NotIDed _ -> None

  let pred_to_str = function
    | P1 p -> IDs.id1 ^ S1.pred_to_str p
    | P2 p -> IDs.id2 ^ S2.pred_to_str p

  let list_preds () =
    List.map (fun (p, ins, outs) -> (P1 p, ins, outs)) (S1.list_preds ())
    @ List.map (fun (p, ins, outs) -> (P2 p, ins, outs)) (S2.list_preds ())

  type c_fix_t = F1 of S1.c_fix_t | F2 of S2.c_fix_t [@@deriving show]
  type err_t = E1 of S1.err_t | E2 of S2.err_t [@@deriving show, yojson]

  let empty () : t = (S1.empty (), S2.empty ())

  let execute_action action (s1, s2) args =
    let open Delayed.Syntax in
    match action with
    | A1 action -> (
        let+ r1 = S1.execute_action action s1 args in
        match r1 with
        | Ok (s1', v) -> Ok ((s1', s2), v)
        | Error e -> Error (E1 e))
    | A2 action -> (
        let+ r2 = S2.execute_action action s2 args in
        match r2 with
        | Ok (s2', v) -> Ok ((s1, s2'), v)
        | Error e -> Error (E2 e))

  let consume pred (s1, s2) args =
    let open Delayed.Syntax in
    match pred with
    | P1 pred -> (
        let+ r1 = S1.consume pred s1 args in
        match r1 with
        | Ok (s1', v) -> Ok ((s1', s2), v)
        | Error e -> Error (E1 e))
    | P2 pred -> (
        let+ r2 = S2.consume pred s2 args in
        match r2 with
        | Ok (s2', v) -> Ok ((s1, s2'), v)
        | Error e -> Error (E2 e))

  let produce pred (s1, s2) args =
    let open Delayed.Syntax in
    match pred with
    | P1 pred ->
        let+ s1' = S1.produce pred s1 args in
        (s1', s2)
    | P2 pred ->
        let+ s2' = S2.produce pred s2 args in
        (s1, s2')

  let compose (s1a, s2a) (s1b, s2b) =
    let open Delayed.Syntax in
    let* s1' = S1.compose s1a s1b in
    let+ s2' = S2.compose s2a s2b in
    (s1', s2')

  let is_fully_owned (s1, s2) e =
    Formula.Infix.((S1.is_fully_owned s1 e) #&& (S2.is_fully_owned s2 e))

  let is_empty (s1, s2) = S1.is_empty s1 && S2.is_empty s2

  let instantiate v =
    let s1, v1 = S1.instantiate v in
    let s2, v2 = S2.instantiate v in
    ((s1, s2), v1 @ v2)
  (* Maybe forbid it? *)

  let substitution_in_place st (s1, s2) =
    let open Delayed.Syntax in
    let* s1' = S1.substitution_in_place st s1 in
    let+ s2' = S2.substitution_in_place st s2 in
    (s1', s2')

  let lvars (s1, s2) = Containers.SS.union (S1.lvars s1) (S2.lvars s2)
  let alocs (s1, s2) = Containers.SS.union (S1.alocs s1) (S2.alocs s2)

  let assertions (s1, s2) =
    let a1 = S1.assertions s1 in
    let a1 = List.map (fun (p, i, o) -> (P1 p, i, o)) a1 in
    let a2 = S2.assertions s2 in
    let a2 = List.map (fun (p, i, o) -> (P2 p, i, o)) a2 in
    a1 @ a2

  let assertions_others (s1, s2) =
    S1.assertions_others s1 @ S2.assertions_others s2

  let get_recovery_tactic (s1, s2) = function
    | E1 e -> S1.get_recovery_tactic s1 e
    | E2 e -> S2.get_recovery_tactic s2 e

  let get_fixes (s1, s2) pfs tenv = function
    | E1 e ->
        let fixes = S1.get_fixes s1 pfs tenv e in
        List.map
          (fun (f, fs, vs, ss) -> (List.map (fun f -> F1 f) f, fs, vs, ss))
          fixes
    | E2 e ->
        let fixes = S2.get_fixes s2 pfs tenv e in
        List.map
          (fun (f, fs, vs, ss) -> (List.map (fun f -> F2 f) f, fs, vs, ss))
          fixes

  let can_fix = function
    | E1 e -> S1.can_fix e
    | E2 e -> S2.can_fix e

  let apply_fix (s1, s2) =
    let open Delayed.Syntax in
    function
    | F1 f -> (
        let+ s1' = S1.apply_fix s1 f in
        match s1' with
        | Ok s1' -> Ok (s1', s2)
        | Error e -> Error (E1 e))
    | F2 f -> (
        let+ s2' = S2.apply_fix s2 f in
        match s2' with
        | Ok s2' -> Ok (s1, s2')
        | Error e -> Error (E2 e))
end
