open Gillian.Utils
open Gillian.Monadic
(* open Gillian.Symbolic*)
open Gil_syntax
module DSR = DelayedSymResult

module Freed = struct
    type c_fix_t = FAddState [@@deriving show]
    type err_t = | UseAfterFree | DoubleFree [@@deriving show, yojson]
    type miss_t = MissingState [@@deriving show, yojson]
    type action = unit
    type pred = | Freed

    type t = unit option [@@deriving show, yojson]


    let action_from_str _ = None

    let action_to_str () = ""

    let list_actions () = [ ]

    let pred_from_str = function
      | "freed" -> Some Freed
      | _ -> None

    let pred_to_str Freed ="freed"

    let list_preds () = [ (Freed, [], []) ]
    let empty () : t = None

    let execute_action () _ _ = failwith "Invalid Freed action"

    let consume Freed s args =
      match (s, args) with
      | Some (), [] -> DSR.ok (None, [ ])
      | None, [] -> DSR.miss MissingState
      | _, _ -> failwith "Invalid Freed consume"

    let produce Freed s args =
      match (s, args) with
      | None, [ ] -> Delayed.return (Some ())
      | Some _, [] -> Delayed.vanish ()
      | _, _ -> failwith "Invalid PointsTo produce"

    let substitution_in_place _ (heap : t) = Delayed.return heap

    let compose s1 s2 =
      match (s1, s2) with
      | None, _ -> Delayed.return s2
      | _, None -> Delayed.return s1
      | _ -> Delayed.vanish ()

    let is_fully_owned = function
      | None -> Formula.False
      | Some _ -> Formula.True

    let is_empty = function
      | None -> true
      | Some _ -> false

    let instantiate = function
      | [] -> Some ()
      | _ -> failwith "Invalid Freed instantiation"

    let lvars _ = Containers.SS.empty

    let alocs _ =Containers.SS.empty

    let assertions = function
      | None -> []
      | Some () -> [ (Freed, [], [ ]) ]

    let get_recovery_tactic _ = function
      | MissingState -> Gillian.General.Recovery_tactic.none

    let get_fixes _ _ _ _ = []

    let apply_fix _ FAddState = DSR.ok (Some ())
end

module Make (S : MyMonadicSMemory.S) : MyMonadicSMemory.S = struct
  module Sum = Sum.Make (struct let id1 = "" let id2 = ""  end) (S) (Freed)
  include Sum

  let pred_from_str = function
    | "freed" -> Some (P2 Freed.Freed)
    | s -> Option.map (fun p -> P1 p) (S.pred_from_str s)

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

  let execute_action action (s: t) args =
    match (action, s) with
    | SubAction a, S1 s ->
        let+^ s', outs = S.execute_action a s args in
        if S.is_empty s' then (None, outs) else (S1 s', outs)
    | SubAction a, None ->
        let+^ s', outs = S.execute_action a (S.empty ()) args in
        if S.is_empty s' then (None, outs) else (S1 s', outs)
    | SubAction _, S2 _ -> DSR.lfail (E2 UseAfterFree)
    | Free, S1 s ->
        if%sat S.is_fully_owned s then DSR.ok (S2 (Some ()), [])
        else DSR.miss MissingState
    | Free, S2 _ -> DSR.lfail (E2 DoubleFree)
    | Free, None -> DSR.miss MissingState

end
