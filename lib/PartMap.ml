open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

module type PartMapIndex = sig
  include Prelude.Map.OrderedType
  val pp : Format.formatter -> t -> unit
  val of_val : Expr.t -> t
  val substitute: Subst.t -> t -> t
end

module Make
  (I: PartMapIndex)
  (S: MyMonadicSMemory.S) : MyMonadicSMemory.S = struct

  (* TODO: This is all wrong, states in the map are not accessed like this
     (see MList for something more accurate) *)

  module SMap = Prelude.Map.Make (I)

  type c_fix_t =
  | FAddIndex of I.t
  | FInnerFix of I.t * S.c_fix_t
  [@@deriving show]

  type err_t =
  | IndexNotInArgs
  | MissingIndex of I.t
  | InnerError of I.t * S.err_t
  [@@deriving show, yojson]

  type t = S.t SMap.t
  [@@deriving yojson]

  let show s = "can't pp PartMap yet"
  let pp fmt s = Format.fprintf fmt "%s" (show s)

  type action = S.action
  let action_from_str = S.action_from_str
  type pred = S.pred
  let pred_from_str = S.pred_from_str
  let pred_to_str = S.pred_to_str

  let map_entries s f =
    SMap.to_list s
    |> List.map (fun (idx, s) -> f s)

  let init (): t = SMap.empty

  let clear s = s
  let construct _ = failwith "Implement here (construct)"

  let execute_action action a args =
    let open Delayed.Syntax in
    match args with
    | [] -> Delayed.return (Error IndexNotInArgs)
    | idx :: args ->
      let idx = I.of_val idx in
      match SMap.find_opt idx a with
      | None -> Delayed.return (Error (MissingIndex idx))
      | Some s ->
        let+ result = S.execute_action action s args in
        match result with
        | Ok (s', args') -> Ok (SMap.add idx s' a, args')
        | Error e -> Error (InnerError (idx, e))

  let consume pred s args =
    let open Delayed.Syntax in
    match args with
    | [] -> Delayed.return (Error IndexNotInArgs)
    | idx :: args ->
      let idx = I.of_val idx in
      match SMap.find_opt idx s with
      | None -> Delayed.return (Error (MissingIndex idx))
      | Some ss ->
        let+ result = S.consume pred ss args in
        match result with
        | Ok (ss', args') -> Ok (SMap.add idx ss' s, args')
        | Error e -> Error (InnerError (idx, e))

  let produce pred s args =
    let open Delayed.Syntax in
    match args with
    | [] -> Delayed.return s
    | idx :: args ->
      let idx = I.of_val idx in
      match SMap.find_opt idx s with
      | None -> Delayed.return s
      | Some ss ->
        let+ ss' = S.produce pred ss args in
        SMap.add idx ss' s

  let compose s1 s2 = failwith "Implement here (compose)"

  let substitution_in_place sub s =
    let open Delayed.Syntax in
    let mapper (idx, s) =
      let+ s' = S.substitution_in_place sub s in
      let idx' = I.substitute sub idx in (idx', s') in
    let map_entries = SMap.bindings s in
    let+ sub_entries = Delayed.all (List.map mapper map_entries) in
    let merge v opt = match opt with (* if entry exists, merge the values *)
      | None -> Some v
      | Some v' -> Some (S.compose v v') in
    List.fold_left (fun acc (idx, s) -> SMap.update idx (merge s) acc) SMap.empty sub_entries

  let lvars s =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.lvars s)) s empty

  let alocs s =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.alocs s)) s empty

  let assertions s = map_entries s S.assertions |> List.flatten
  let get_recovery_tactic (s:t) (e:err_t) = match e with
    | InnerError (idx, e) -> S.get_recovery_tactic (SMap.find idx s) e
    | _ -> failwith "Implement here (get_recovery_tactic)"

  let get_fixes s pfs tenv e = match e with
    | InnerError (idx, e) ->
      let fixes = S.get_fixes (SMap.find idx s) pfs tenv e in
      List.map (fun (f, fs, vs, ss) -> (List.map (fun f -> FInnerFix (idx, f)) f, fs, vs, ss)) fixes
    | _ -> failwith "Implement here (get_fixes)"

  let can_fix e = match e with
    | InnerError (idx, e) -> S.can_fix e
    | _ -> failwith "Implement here (can_fix)"

  let apply_fix (s:t) f =
    let open Delayed.Syntax in
    match f with
    | FInnerFix (idx, f) ->
      let ss = SMap.find idx s in
      let+ ss' = S.apply_fix ss f in
      (match ss' with
      | Ok ss' -> Ok (SMap.add idx ss' s)
      | Error e -> Error (InnerError (idx, e)))
    | _ -> failwith "Implement here (apply_fix)"

end
