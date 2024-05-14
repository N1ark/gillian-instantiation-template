open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
open SymResult
module DSR = DelayedSymResult

module Make (S : MyMonadicSMemory.S) : MyMonadicSMemory.S = struct
  type t = None | Freed | SubState of S.t [@@deriving yojson, show]
  type c_fix_t = S.c_fix_t [@@deriving show]

  type err_t = DoubleFree | UseAfterFree | SubError of S.err_t
  [@@deriving show, yojson]

  type miss_t = MissingResource | SubMiss of S.miss_t
  [@@deriving show, yojson]

  type action = Free | SubAction of S.action

  let action_from_str = function
    | "free" -> Some Free
    | str -> Option.map (fun a -> SubAction a) (S.action_from_str str)

  let action_to_str = function
    | Free -> "free"
    | SubAction a -> S.action_to_str a

  let list_actions () =
    (Free, [], [])
    :: List.map
         (fun (a, arg, ret) -> (SubAction a, arg, ret))
         (S.list_actions ())

  type pred = FreedPred | SubPred of S.pred

  let pred_from_str = function
    | "freed" -> Some FreedPred
    | str -> Option.map (fun p -> SubPred p) (S.pred_from_str str)

  let pred_to_str = function
    | FreedPred -> "freed"
    | SubPred p -> S.pred_to_str p

  let list_preds () =
    (FreedPred, [], [])
    :: List.map (fun (p, ins, outs) -> (SubPred p, ins, outs)) (S.list_preds ())

  let empty () : t = None

  let map_lift f = function
    | Ok x -> Ok (f x)
    | LFail e -> LFail (SubError e)
    | Miss m -> Miss (SubMiss m)

  let ( let+^ ) x f = Delayed.map x (map_lift f)

  let simplify = function
    | s when S.is_empty s -> None
    | s -> SubState s

  let execute_action action s (args : Values.t list) :
      (t * Values.t list, err_t, miss_t) DSR.t =
    match (action, s) with
    | SubAction a, SubState s ->
        let+^ s', outs = S.execute_action a s args in
        (simplify s', outs)
    | SubAction a, None ->
        let+^ s', outs = S.execute_action a (S.empty ()) args in
        (simplify s', outs)
    | SubAction _, Freed -> DSR.lfail UseAfterFree
    | Free, SubState s ->
        if%sat S.is_fully_owned s then DSR.ok (Freed, [])
        else DSR.miss MissingResource
    | Free, Freed -> DSR.lfail DoubleFree
    | Free, None -> DSR.miss MissingResource

  let consume pred s ins =
    match (pred, s) with
    | SubPred p, SubState s ->
        let+^ s', outs = S.consume p s ins in
        (simplify s', outs)
    | SubPred _, Freed -> DSR.lfail UseAfterFree
    | SubPred p, None ->
        let+^ s', outs = S.consume p (S.empty ()) ins in
        (simplify s', outs)
    | FreedPred, SubState _ -> DSR.lfail UseAfterFree
    | FreedPred, Freed -> DSR.ok (empty (), [])
    | FreedPred, None -> DSR.miss MissingResource

  let produce pred s args =
    let open Delayed.Syntax in
    match (pred, s) with
    | SubPred p, SubState s ->
        let+ s' = S.produce p s args in
        SubState s'
    | SubPred _, Freed -> Delayed.vanish ()
    | SubPred p, None ->
        let+ s' = S.produce p (S.empty ()) args in
        SubState s'
    | FreedPred, SubState _ -> Delayed.vanish ()
    | FreedPred, Freed -> Delayed.vanish ()
    | FreedPred, None -> Delayed.return Freed

  let compose s1 s2 =
    let open Delayed.Syntax in
    match (s1, s2) with
    | None, s | s, None -> Delayed.return s
    | SubState s1, SubState s2 ->
        let+ s' = S.compose s1 s2 in
        SubState s'
    | _ -> Delayed.vanish ()

  let is_fully_owned = function
    | SubState s -> S.is_fully_owned s
    | Freed -> Formula.True
    | None -> Formula.False

  let is_empty = function
    | SubState s -> S.is_empty s
    | Freed -> false
    | None -> true

  let instantiate v = SubState (S.instantiate v)

  let substitution_in_place sub s =
    let open Delayed.Syntax in
    match s with
    | SubState s ->
        let+ s' = S.substitution_in_place sub s in
        SubState s'
    | s -> Delayed.return s

  let lvars = function
    | SubState s -> S.lvars s
    | _ -> Containers.SS.empty

  let alocs = function
    | SubState s -> S.alocs s
    | _ -> Containers.SS.empty

  let assertions = function
    | SubState s ->
        List.map (fun (p, i, o) -> (SubPred p, i, o)) (S.assertions s)
    | Freed -> [ (FreedPred, [], []) ]
    | None -> []

  let get_recovery_tactic s e =
    match (s, e) with
    | SubState s, SubMiss e -> S.get_recovery_tactic s e
    | _ -> Gillian.General.Recovery_tactic.none (* TODO *)

  let get_fixes s pfs tenv e =
    match (e, s) with
    | SubMiss e, SubState s -> S.get_fixes s pfs tenv e
    | _ -> [] (* TODO *)

  let apply_fix s f =
    match s with
    | None ->
        let+^ s' = S.apply_fix (S.empty ()) f in
        simplify s'
    | SubState s ->
        let+^ s' = S.apply_fix s f in
        simplify s'
    | Freed -> DSR.lfail UseAfterFree
end
