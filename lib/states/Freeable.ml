open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

type 'a freeable = None | Freed | SubState of 'a [@@deriving yojson, show]

module Make (S : MyMonadicSMemory.S) :
  MyMonadicSMemory.S with type t = S.t freeable = struct
  type t = S.t freeable [@@deriving yojson, show]
  type c_fix_t = SubFix of S.c_fix_t | AddFreed [@@deriving show]

  let pp fmt = function
    | None -> Fmt.string fmt "None"
    | Freed -> Fmt.string fmt "Freed"
    | SubState s -> S.pp fmt s

  type err_t =
    | DoubleFree
    | UseAfterFree
    | NotEnoughResourceToFree
    | MissingFreed
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

  let empty () : t = None

  let simplify = function
    | s when S.is_empty s -> None
    | s -> SubState s

  let execute_action action s (args : Values.t list) :
      (t * Values.t list, err_t) DR.t =
    let open Delayed.Syntax in
    match (action, s) with
    | SubAction a, SubState s -> (
        let+ r = S.execute_action a s args in
        match r with
        | Ok (s', outs) -> Ok (simplify s', outs)
        | Error e -> Error (SubError e))
    | SubAction a, None -> (
        let+ r = S.execute_action a (S.empty ()) args in
        match r with
        | Ok (s', outs) -> Ok (simplify s', outs)
        | Error e -> Error (SubError e))
    | SubAction _, Freed -> DR.error UseAfterFree
    | Free, SubState s ->
        if%sat S.is_fully_owned s args then DR.ok (Freed, [])
        else DR.error NotEnoughResourceToFree
    | Free, Freed -> DR.error DoubleFree
    | Free, None -> DR.error NotEnoughResourceToFree

  let consume pred s ins =
    let open Delayed.Syntax in
    match (pred, s) with
    | SubPred p, SubState s -> (
        let+ r = S.consume p s ins in
        match r with
        | Ok (s', outs) -> Ok (simplify s', outs)
        | Error e -> Error (SubError e))
    | SubPred _, Freed -> DR.error UseAfterFree
    | SubPred p, None -> (
        let+ r = S.consume p (S.empty ()) ins in
        match r with
        | Ok (s', outs) -> Ok (simplify s', outs)
        | Error e -> Error (SubError e))
    | FreedPred, SubState _ -> DR.error UseAfterFree
    | FreedPred, Freed -> DR.ok (empty (), [])
    | FreedPred, None -> DR.error MissingFreed

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

  let is_fully_owned s e =
    match s with
    | SubState s -> S.is_fully_owned s e
    | Freed -> Formula.True
    | None -> Formula.False

  let is_empty = function
    | SubState s -> S.is_empty s
    | Freed -> false
    | None -> true

  let instantiate v =
    let s, v = S.instantiate v in
    (SubState s, v)

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

  let assertions_others = function
    | SubState s -> S.assertions_others s
    | _ -> []

  let get_recovery_tactic s e =
    match (s, e) with
    | SubState s, SubError e -> S.get_recovery_tactic s e
    | _ -> Gillian.General.Recovery_tactic.none (* TODO *)

  let can_fix = function
    | SubError e -> S.can_fix e
    | MissingFreed -> true
    | NotEnoughResourceToFree -> false (* TODO: how ? new function? :( *)
    | _ -> false

  let get_fixes s e =
    let open Delayed.Syntax in
    match (e, s) with
    | SubError e, SubState s ->
        let+ fixes = S.get_fixes s e in
        List.map (fun f -> SubFix f) fixes
    | SubError e, None ->
        let base_fixes =
          let+ fixes = S.get_fixes (S.empty ()) e in
          List.map (fun f -> SubFix f) fixes
        in
        let freed_fixes = Delayed.return [ AddFreed ] in
        Delayed.branches [ base_fixes; freed_fixes ]
    | MissingFreed, _ -> Delayed.return [ AddFreed ]
    | _, _ -> failwith "Invalid fix call"

  let apply_fix s f =
    Logging.tmi (fun fm -> fm "Applying fix %a to state %a" pp_c_fix_t f pp s);
    let open Delayed.Syntax in
    match (f, s) with
    | SubFix f, None -> (
        let+ r = S.apply_fix (S.empty ()) f in
        match r with
        | Ok s' -> Ok (simplify s')
        | Error e -> Error (SubError e))
    | SubFix f, SubState s -> (
        let+ r = S.apply_fix s f in
        match r with
        | Ok s' -> Ok (simplify s')
        | Error e -> Error (SubError e))
    | SubFix _, _ -> failwith "Invalid SubFix fix"
    | AddFreed, None -> DR.ok Freed
    | AddFreed, _ -> failwith "Invalid AddState fix"
end
