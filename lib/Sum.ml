open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
open MyUtils

module Make (IDs : IDs) (S1 : MyMonadicSMemory.S) (S2 : MyMonadicSMemory.S) :
  MyMonadicSMemory.S = struct
  type t = None | S1 of S1.t | S2 of S2.t [@@deriving show, yojson]

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
    let a1 =
      List.map (fun (a, args, ret) -> (A1 a, args, ret)) (S1.list_actions ())
    in
    let a2 =
      List.map (fun (a, args, ret) -> (A2 a, args, ret)) (S2.list_actions ())
    in
    a1 @ a2

  type pred = P1 of S1.pred | P2 of S2.pred

  let pred_from_str s =
    match IDer.get_ided s with
    | ID1 s -> Option.map (fun p -> P1 p) (S1.pred_from_str s)
    | ID2 s -> Option.map (fun p -> P2 p) (S2.pred_from_str s)
    | NotIDed _ -> None

  let pred_to_str = function
    (* TODO: make this flexible to allow IDing with eg. suffixes *)
    | P1 p -> IDs.id1 ^ S1.pred_to_str p
    | P2 p -> IDs.id2 ^ S2.pred_to_str p

  let list_preds () =
    let p1 =
      List.map (fun (p, ins, outs) -> (P1 p, ins, outs)) (S1.list_preds ())
    in
    let p2 =
      List.map (fun (p, ins, outs) -> (P2 p, ins, outs)) (S2.list_preds ())
    in
    p1 @ p2

  type c_fix_t = F1 of S1.c_fix_t | F2 of S2.c_fix_t [@@deriving show]

  type err_t = MissingState | E1 of S1.err_t | E2 of S2.err_t
  [@@deriving show, yojson]

  let empty () = None

  let execute_action action s args =
    let open Delayed.Syntax in
    match (action, s) with
    | A1 action, S1 s1 -> (
        let+ res = S1.execute_action action s1 args in
        match res with
        | Ok (s1', args') -> Ok (S1 s1', args')
        | Error e -> Error (E1 e))
    | A2 action, S2 s2 -> (
        let+ res = S2.execute_action action s2 args in
        match res with
        | Ok (s2', args') -> Ok (S2 s2', args')
        | Error e -> Error (E2 e))
    | _, None -> Delayed.return (Error MissingState)
    | A1 _, S2 _ | A2 _, S1 _ ->
        failwith "Sum.execute_action: mismatched arguments"

  let consume pred s args =
    let open Delayed.Syntax in
    match (pred, s) with
    | P1 pred, S1 s1 -> (
        let+ res = S1.consume pred s1 args in
        match res with
        | Ok (s1', args') -> Ok (S1 s1', args')
        | Error e -> Error (E1 e))
    | P2 pred, S2 s2 -> (
        let+ res = S2.consume pred s2 args in
        match res with
        | Ok (s2', args') -> Ok (S2 s2', args')
        | Error e -> Error (E2 e))
    | _, None -> Delayed.return (Error MissingState)
    | P1 _, S2 _ | P2 _, S1 _ -> failwith "Sum.consume: mismatched arguments"

  let produce pred s args =
    let open Delayed.Syntax in
    match (pred, s) with
    | P1 pred, None ->
        let s1 = S1.empty () in
        let+ s1' = S1.produce pred s1 args in
        S1 s1'
    | P1 pred, S1 s1 ->
        let+ s1' = S1.produce pred s1 args in
        S1 s1'
    | P2 pred, None ->
        let s2 = S2.empty () in
        let+ s2' = S2.produce pred s2 args in
        S2 s2'
    | P2 pred, S2 s2 ->
        let+ s2' = S2.produce pred s2 args in
        S2 s2'
    | P1 _, S2 _ | P2 _, S1 _ -> failwith "Sum.produce: mismatched arguments"

  let compose s1 s2 =
    let open Delayed.Syntax in
    match (s1, s2) with
    | None, s | s, None -> Delayed.return s
    | S1 s1, S1 s2 ->
        let+ s' = S1.compose s1 s2 in
        S1 s'
    | S2 s1, S2 s2 ->
        let+ s' = S2.compose s1 s2 in
        S2 s'
    | S1 _, S2 _ | S2 _, S1 _ -> failwith "Sum.compose: mismatched arguments"

  let is_fully_owned = function
    | S1 s1 -> S1.is_fully_owned s1
    | S2 s2 -> S2.is_fully_owned s2
    | None -> Formula.True

  let is_empty = function
    | S1 s1 -> S1.is_empty s1
    | S2 s2 -> S2.is_empty s2
    | None -> true

  let instantiate v = S1 (S1.instantiate v)
  (* TODO: does it even make sense? forbid? *)

  let substitution_in_place st =
    let open Delayed.Syntax in
    function
    | S1 t1 ->
        let+ t1' = S1.substitution_in_place st t1 in
        S1 t1'
    | S2 t2 ->
        let+ t2' = S2.substitution_in_place st t2 in
        S2 t2'
    | None -> Delayed.return None

  let lvars = function
    | S1 s1 -> S1.lvars s1
    | S2 s2 -> S2.lvars s2
    | None -> Containers.SS.empty

  let alocs = function
    | S1 s1 -> S1.alocs s1
    | S2 s2 -> S2.alocs s2
    | None -> Containers.SS.empty

  let assertions = function
    | S1 s1 -> List.map (fun (p, i, o) -> (P1 p, i, o)) (S1.assertions s1)
    | S2 s2 -> List.map (fun (p, i, o) -> (P2 p, i, o)) (S2.assertions s2)
    | None -> []

  let get_recovery_tactic s e =
    match (s, e) with
    | S1 s1, E1 e1 -> S1.get_recovery_tactic s1 e1
    | S2 s2, E2 e2 -> S2.get_recovery_tactic s2 e2
    | _ -> failwith "get_recovery_tactic: mismatched arguments"

  let get_fixes s pfs tenv e =
    match (s, e) with
    | S1 s1, E1 e1 ->
        let fixes = S1.get_fixes s1 pfs tenv e1 in
        List.map
          (fun (fxs, fml, vars, lvars) ->
            (List.map (fun fx -> F1 fx) fxs, fml, vars, lvars))
          fixes
    | S2 s2, E2 e2 ->
        let fixes = S2.get_fixes s2 pfs tenv e2 in
        List.map
          (fun (fxs, fml, vars, lvars) ->
            (List.map (fun fx -> F2 fx) fxs, fml, vars, lvars))
          fixes
    | _ -> failwith "get_fixes: mismatched arguments"

  let can_fix = function
    | E1 s1 -> S1.can_fix s1
    | E2 s2 -> S2.can_fix s2
    | MissingState -> false (* TODO... *)

  let apply_fix s f =
    let open Delayed.Syntax in
    match (s, f) with
    | S1 s1, F1 f1 -> (
        let+ res = S1.apply_fix s1 f1 in
        match res with
        | Ok s1' -> Ok (S1 s1')
        | Error e -> Error (E1 e))
    | S2 s2, F2 f2 -> (
        let+ res = S2.apply_fix s2 f2 in
        match res with
        | Ok s2' -> Ok (S2 s2')
        | Error e -> Error (E2 e))
    | _ -> failwith "apply_fix: mismatched arguments"
end
