open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result
module ExpMap = MyUtils.ExpMap

module Make (S : MyMonadicSMemory.S) :
  MyMonadicSMemory.S with type t = S.t ExpMap.t * Expr.t option = struct
  type t = S.t ExpMap.t * Expr.t option [@@deriving yojson]

  let pp fmt ((b, n) : t) =
    Fmt.pf fmt "@[<v>BOUND: %a@ %a@]"
      (Fmt.option ~none:(Fmt.any "NONE") Expr.pp)
      n
      (Fmt.braces @@ Fmt.vbox
      @@ Fmt.iter_bindings ~sep:Fmt.sp ExpMap.iter
      @@ fun ft (o, v) -> Fmt.pf ft "%a: %a" Expr.pp o S.pp v)
      b

  type err_t =
    | OutOfBounds of Expr.t * Expr.t (* Accessed index, list length *)
    | MissingLength
    | SubError of Expr.t * S.err_t
  [@@deriving show, yojson]

  type action = SubAction of S.action

  let action_from_str str =
    Option.map (fun a -> SubAction a) (S.action_from_str str)

  let action_to_str = function
    | SubAction a -> S.action_to_str a

  let list_actions () =
    List.map
      (fun (a, args, ret) -> (SubAction a, "offset" :: args, ret))
      (S.list_actions ())

  type pred = Length | SubPred of S.pred

  let pred_from_str = function
    | "length" -> Some Length
    | str -> Option.map (fun p -> SubPred p) (S.pred_from_str str)

  let pred_to_str = function
    | Length -> "length"
    | SubPred p -> S.pred_to_str p

  let list_preds () =
    (Length, [], [ "length" ])
    :: List.map
         (fun (p, args, ret) -> (SubPred p, "offset" :: args, ret))
         (S.list_preds ())

  let init = S.init
  let empty () : t = (ExpMap.empty, None)

  let validate_index (_, n) idx =
    let open Delayed.Syntax in
    let* idx = Delayed.reduce idx in
    match n with
    | Some n ->
        if%sat Formula.Infix.(Expr.zero_i #<= idx #&& (idx #< n)) then DR.ok ()
        else DR.error (OutOfBounds (idx, n))
    | None -> DR.ok ()

  let execute_action action ((b, n) : t) (args : Values.t list) :
      (t * Values.t list, err_t) DR.t =
    let open DR.Syntax in
    let open Delayed.Syntax in
    match (action, args) with
    | SubAction a, idx :: args -> (
        let** () = validate_index (b, n) idx in
        let* idx, s = ExpMap.sym_find_default idx b ~default:S.empty in
        let+ r = S.execute_action a s args in
        match r with
        | Ok (s', v) -> Ok ((ExpMap.add idx s' b, n), v)
        | Error e -> Error (SubError (idx, e)))
    | SubAction _, [] -> failwith "Missing index for sub-action"

  let consume pred (b, n) ins =
    let open DR.Syntax in
    let open Delayed.Syntax in
    match (pred, ins) with
    | SubPred p, idx :: ins -> (
        let** () = validate_index (b, n) idx in
        let* idx, s = ExpMap.sym_find_default idx b ~default:S.empty in
        let+ r = S.consume p s ins in
        match r with
        | Ok (s, outs) when S.is_empty s -> Ok ((ExpMap.remove idx b, n), outs)
        | Ok (s, outs) -> Ok ((ExpMap.add idx s b, n), outs)
        | Error e -> Error (SubError (idx, e)))
    | SubPred _, [] -> failwith "Missing index for sub-predicate consume"
    | Length, [] -> (
        match n with
        | Some n -> DR.ok ((b, None), [ n ])
        | None -> DR.error MissingLength)
    | Length, _ -> failwith "Invalid arguments for length consume"

  let produce pred (b, n) args =
    let open Delayed.Syntax in
    let open MyUtils.Syntax in
    match (pred, args) with
    | SubPred p, idx :: args ->
        let*? _ = validate_index (b, n) idx in
        let* idx, s = ExpMap.sym_find_default idx b ~default:S.empty in
        let* s' = S.produce p s args in
        Delayed.return (ExpMap.add idx s' b, n)
    | SubPred _, [] -> failwith "Missing index for sub-predicate produce"
    | Length, [ n' ] -> (
        match n with
        | Some _ ->
            Logging.normal (fun m ->
                m "Warning MList: vanishing due to duplicate length");
            Delayed.vanish ()
        | None -> Delayed.return (b, Some n'))
    | Length, _ -> failwith "Invalid arguments for length produce"

  let compose s1 s2 =
    match (s1, s2) with
    | (b1, n), (b2, None) | (b1, None), (b2, n) ->
        let open Delayed.Syntax in
        let* b' = ExpMap.sym_merge S.compose b1 b2 in
        Delayed.return (b', n)
    | (_, Some _), (_, Some _) -> Delayed.vanish ()

  let is_fully_owned s e =
    let open Formula.Infix in
    match s with
    | b, Some _ ->
        ExpMap.fold
          (fun _ v acc -> acc #&& (S.is_fully_owned v e))
          b Formula.True
    | _, None -> Formula.False

  let is_empty = function
    | b, None -> ExpMap.for_all (fun _ v -> S.is_empty v) b
    | _ -> false

  let is_concrete = function
    | b, None -> ExpMap.for_all (fun _ v -> S.is_concrete v) b
    | b, Some n ->
        ExpMap.for_all (fun _ v -> S.is_concrete v) b && Expr.is_concrete n

  let instantiate : Expr.t list -> t * Expr.t list = function
    | n :: args ->
        let length =
          match n with
          | Expr.Lit (Int n) -> Z.to_int n
          | _ -> failwith "Invalid length for list instantiation"
        in
        let rec aux acc i =
          if i = length then acc
          else
            aux (ExpMap.add (Expr.int i) (fst (S.instantiate args)) acc) (i + 1)
        in
        let b = aux ExpMap.empty 0 in
        ((b, Some n), [])
    | [] -> failwith "Invalid arguments for list instantiation"

  let substitution_in_place sub (b, n) =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = Subst.subst_in_expr sub idx ~partial:true in
      (idx', s')
    in
    let map_entries = ExpMap.bindings b in
    let* sub_entries = Delayed.all (List.map mapper map_entries) in
    let+ b' =
      ExpMap.sym_compose ~matching:false S.compose sub_entries ExpMap.empty
    in
    let n' = Option.map (Subst.subst_in_expr sub ~partial:true) n in
    (b', n')

  let lvars (b, n) =
    let open Containers.SS in
    let lvars_map =
      ExpMap.fold
        (fun k v acc -> union (union (Expr.lvars k) (S.lvars v)) acc)
        b empty
    in
    match n with
    | Some n -> union lvars_map (Expr.lvars n)
    | None -> lvars_map

  let alocs (b, n) =
    let open Containers.SS in
    let alocs_map =
      ExpMap.fold
        (fun k v acc -> union (union (Expr.alocs k) (S.alocs v)) acc)
        b empty
    in
    match n with
    | Some n -> union alocs_map (Expr.alocs n)
    | None -> alocs_map

  let lift_corepred k (p, i, o) = (SubPred p, k :: i, o)

  let assertions (b, n) =
    let sub_asrts =
      ExpMap.fold
        (fun k v acc -> acc @ List.map (lift_corepred k) (S.assertions v))
        b []
    in
    match n with
    | Some n -> (Length, [], [ n ]) :: sub_asrts
    | None -> sub_asrts

  let assertions_others (b, _) =
    List.concat_map (fun (_, v) -> S.assertions_others v) (ExpMap.bindings b)

  let get_recovery_tactic (b, _) = function
    | SubError (idx, e) ->
        let s = ExpMap.find_opt idx b |> Option.value ~default:(S.empty ()) in
        S.get_recovery_tactic s e
    | _ -> Gillian.General.Recovery_tactic.none

  let can_fix = function
    | SubError (_, e) -> S.can_fix e
    | MissingLength -> true
    | OutOfBounds _ -> false

  let get_fixes = function
    | SubError (idx, e) ->
        S.get_fixes e |> MyUtils.deep_map (MyAsrt.map_cp (lift_corepred idx))
    | MissingLength ->
        let lvar = LVar.alloc () in
        [
          [
            MyAsrt.CorePred (Length, [], [ Expr.LVar lvar ]);
            MyAsrt.Types [ (lvar, Type.IntType) ];
          ];
        ]
    | _ -> failwith "Called get_fixes on unfixable error"
end
