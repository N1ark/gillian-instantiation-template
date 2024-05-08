open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

module Make (S : MyMonadicSMemory.S) : MyMonadicSMemory.S = struct
  type t = Freed | SubState of S.t [@@deriving yojson, show]
  type c_fix_t = SubFix of S.c_fix_t [@@deriving show]

  type err_t =
    | DoubleFree
    | UseAfterFree
    | MissingResource
    | SubError of S.err_t
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

  let empty () : t = SubState (S.empty ())

  let execute_action action s (args : Values.t list) :
      (t * Values.t list, err_t) DR.t =
    let open Delayed.Syntax in
    match (action, s) with
    | SubAction a, SubState s -> (
        let+ r = S.execute_action a s args in
        match r with
        | Ok (s', outs) -> Ok (SubState s', outs)
        | Error e -> Error (SubError e))
    | SubAction _, Freed -> DR.error UseAfterFree
    | Free, SubState s ->
        if%sat S.is_fully_owned s then DR.ok (Freed, [])
        else DR.error MissingResource
    | Free, Freed -> DR.error DoubleFree

  let consume pred s ins =
    let open Delayed.Syntax in
    match (pred, s) with
    | SubPred p, SubState s -> (
        let+ r = S.consume p s ins in
        match r with
        | Ok (s', outs) -> Ok (SubState s', outs)
        | Error e -> Error (SubError e))
    | SubPred _, Freed -> DR.error UseAfterFree
    | FreedPred, SubState _ -> DR.error UseAfterFree
    | FreedPred, Freed -> DR.ok (empty (), [])
  (* /\ TODO: is Freed omnipotent? Or do we need a third state for "Empty"? *)

  let produce pred s args =
    let open Delayed.Syntax in
    match (pred, s) with
    | SubPred p, SubState s ->
        let+ s' = S.produce p s args in
        SubState s'
    | SubPred _, Freed -> Delayed.vanish ()
    | FreedPred, SubState _ -> Delayed.return Freed (* Not sure... *)
    | FreedPred, Freed -> Delayed.vanish ()

  let compose s1 s2 =
    let open Delayed.Syntax in
    match (s1, s2) with
    | SubState s1, SubState s2 ->
        let+ s' = S.compose s1 s2 in
        SubState s'
    | Freed, SubState s2 when S.is_empty s2 -> Delayed.return Freed
    | SubState s1, Freed when S.is_empty s1 -> Delayed.return Freed
    (* | Freed, Freed -> Delayed.return Freed are there cases where we want this? *)
    | _ -> Delayed.vanish ()

  let is_fully_owned = function
    | SubState s -> S.is_fully_owned s
    | Freed -> Formula.True

  let is_empty = function
    | SubState s -> S.is_empty s
    | Freed -> false

  let instantiate v = SubState (S.instantiate v)

  let substitution_in_place sub s =
    let open Delayed.Syntax in
    match s with
    | SubState s ->
        let+ s' = S.substitution_in_place sub s in
        SubState s'
    | Freed -> Delayed.return Freed

  let lvars = function
    | SubState s -> S.lvars s
    | Freed -> Containers.SS.empty

  let alocs = function
    | SubState s -> S.alocs s
    | Freed -> Containers.SS.empty

  let assertions = function
    | SubState s ->
        List.map (fun (p, i, o) -> (SubPred p, i, o)) (S.assertions s)
    | Freed -> [ (FreedPred, [], []) ]

  let get_recovery_tactic s e =
    match (s, e) with
    | SubState s, SubError e -> S.get_recovery_tactic s e
    | _ -> Gillian.General.Recovery_tactic.none (* TODO *)

  let get_fixes s pfs tenv e =
    match (e, s) with
    | SubError e, SubState s ->
        let mapper (fs, fml, t, c) =
          (List.map (fun f -> SubFix f) fs, fml, t, c)
        in
        List.map mapper (S.get_fixes s pfs tenv e)
    | _ -> [] (* TODO *)

  let can_fix = function
    | SubError e -> S.can_fix e
    | MissingResource -> true (* TODO *)
    | _ -> false

  let apply_fix s f =
    match (s, f) with
    | SubState s, SubFix f -> (
        let open Delayed.Syntax in
        let+ r = S.apply_fix s f in
        match r with
        | Ok s' -> Ok (SubState s')
        | Error e -> Error (SubError e))
    | Freed, SubFix _ -> failwith "Cannot apply subfix to freed state"
end
