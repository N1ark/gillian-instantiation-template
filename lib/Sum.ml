open Gillian.Utils
open Gillian.Monadic
open Gil_syntax
open MyUtils
open SymResult
module DSR = DelayedSymResult

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
    List.map (fun (a, args, ret) -> (A1 a, args, ret)) (S1.list_actions ())
    @ List.map (fun (a, args, ret) -> (A2 a, args, ret)) (S2.list_actions ())

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
    List.map (fun (p, ins, outs) -> (P1 p, ins, outs)) (S1.list_preds ())
    @ List.map (fun (p, ins, outs) -> (P2 p, ins, outs)) (S2.list_preds ())

  type c_fix_t = F1 of S1.c_fix_t | F2 of S2.c_fix_t [@@deriving show]

  type err_t = MismatchedState | E1 of S1.err_t | E2 of S2.err_t
  [@@deriving show, yojson]

  type miss_t = MissingState | M1 of S1.miss_t | M2 of S2.miss_t
  [@@deriving show, yojson]

  let empty () = None

  let get_s1 = function
    | S1 s1 -> DSR.ok s1
    | None -> DSR.ok (S1.empty ())
    | S2 _ -> DSR.lfail MismatchedState

  let get_s1_ex = function
    | S1 s1 -> s1
    | None -> S1.empty ()
    | S2 _ -> failwith "MismatchedState"

  let get_s2 = function
    | S2 s2 -> DSR.ok s2
    | None -> DSR.ok (S2.empty ())
    | S1 _ -> DSR.lfail MismatchedState

  let get_s2_ex = function
    | S2 s2 -> s2
    | None -> S2.empty ()
    | S1 _ -> failwith "MismatchedState"

  let execute_action action s args =
    let open Delayed.Syntax in
    let open DSR.Syntax in
    match action with
    | A1 action -> (
        let** s1 = get_s1 s in
        let+ res = S1.execute_action action s1 args in
        match res with
        | Ok (s1', v) when S1.is_empty s1' -> Ok (None, v)
        | Ok (s1', v) -> Ok (S1 s1', v)
        | LFail e -> LFail (E1 e)
        | Miss m -> Miss (M1 m))
    | A2 action -> (
        let** s2 = get_s2 s in
        let+ res = S2.execute_action action s2 args in
        match res with
        | Ok (s2', v) when S2.is_empty s2' -> Ok (None, v)
        | Ok (s2', v) -> Ok (S2 s2', v)
        | LFail e -> LFail (E2 e)
        | Miss m -> Miss (M2 m))

  let consume pred s ins =
    let open Delayed.Syntax in
    let open DSR.Syntax in
    match pred with
    | P1 pred -> (
        let** s1 = get_s1 s in
        let+ res = S1.consume pred s1 ins in
        match res with
        | Ok (s1', outs) when S1.is_empty s1' -> Ok (None, outs)
        | Ok (s1', outs) -> Ok (S1 s1', outs)
        | LFail e -> LFail (E1 e)
        | Miss m -> Miss (M1 m))
    | P2 pred -> (
        let** s2 = get_s2 s in
        let+ res = S2.consume pred s2 ins in
        match res with
        | Ok (s2', outs) when S2.is_empty s2' -> Ok (None, outs)
        | Ok (s2', outs) -> Ok (S2 s2', outs)
        | LFail e -> LFail (E2 e)
        | Miss m -> Miss (M2 m))

  let produce pred s args =
    let open Delayed.Syntax in
    let open DSR.Syntax in
    match pred with
    | P1 pred ->
        let*? s1 = get_s1 s in
        let+ s1' = S1.produce pred s1 args in
        S1 s1'
    | P2 pred ->
        let*? s2 = get_s2 s in
        let+ s2' = S2.produce pred s2 args in
        S2 s2'

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
    (* Technically these two branches aren't needed because we automatically switch to None if
       the state is empty after consume/execute action... *)
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

  let get_recovery_tactic s = function
    | M1 m1 -> S1.get_recovery_tactic (get_s1_ex s) m1
    | M2 m2 -> S2.get_recovery_tactic (get_s2_ex s) m2
    | MissingState -> failwith "get_recovery_tactic: missing state"

  let get_fixes s pfs tenv =
    let fix_mapper f =
      List.map (fun (fxs, fml, vars, lvars) ->
          (List.map f fxs, fml, vars, lvars))
    in
    function
    | M1 m1 ->
        S1.get_fixes (get_s1_ex s) pfs tenv m1 |> fix_mapper (fun fx -> F1 fx)
    | M2 m2 ->
        S2.get_fixes (get_s2_ex s) pfs tenv m2 |> fix_mapper (fun fx -> F2 fx)
    | MissingState -> failwith "get_fixes: missing state"

  let apply_fix s =
    let open Delayed.Syntax in
    let open DSR.Syntax in
    function
    | F1 f1 -> (
        let** s1 = get_s1 s in
        let+ res = S1.apply_fix s1 f1 in
        match res with
        | Ok s1' -> Ok (S1 s1')
        | LFail e -> LFail (E1 e)
        | Miss m -> Miss (M1 m))
    | F2 f2 -> (
        let** s2 = get_s2 s in
        let+ res = S2.apply_fix s2 f2 in
        match res with
        | Ok s2' -> Ok (S2 s2')
        | LFail e -> LFail (E2 e)
        | Miss m -> Miss (M2 m))
end
