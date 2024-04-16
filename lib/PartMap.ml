

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

module type PartMapCodomain = sig
  include Gillian.Monadic.MonadicSMemory.S
  val compose : t -> t -> t
end

module PartMap
  (I: PartMapIndex)
  (S: PartMapCodomain) : Gillian.Monadic.MonadicSMemory.S = struct


  module SMap = Prelude.Map.Make (I)

  type init_data = unit

  type vt = S.vt

  type st = Subst.t

  type c_fix_t =
  | FAddIndex of I.t
  | FInnerFix of I.t * S.c_fix_t

  type err_t =
  | IndexNotInArgs
  | MissingIndex of I.t
  | InnerError of I.t * S.err_t
  [@@deriving show, yojson]

  type t = S.t SMap.t [@@deriving yojson]

  type action_ret = (t * vt list, err_t) result

  let map_entries s f =
    SMap.to_list s
    |> List.map (fun (idx, s) -> f s)

  let init (_:init_data): t = SMap.empty

  let get_init_data (_:t): init_data = ()
  let clear s = s

  (* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
  let execute_action ~(action_name:string) (a:t) (args:vt list) : action_ret Delayed.t =
    let open Delayed.Syntax in
    match args with
    | [] -> Delayed.return (Error IndexNotInArgs)
    | idx :: args ->
      let idx = I.of_val idx in
      match SMap.find_opt idx a with
      | None -> Delayed.return (Error (MissingIndex idx))
      | Some s ->
        let+ result = S.execute_action ~action_name s args in
        match result with
        | Ok (s', args') -> Ok (SMap.add idx s' a, args')
        | Error e -> Error (InnerError (idx, e))


    (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
  let consume ~(core_pred:string) (a:t) (args:vt list) : action_ret Delayed.t =
    let open Delayed.Syntax in
    match args with
    | [] -> Delayed.return (Error IndexNotInArgs)
    | idx :: args ->
      let idx = I.of_val idx in
      match SMap.find_opt idx a with
      | None -> Delayed.return (Error (MissingIndex idx))
      | Some s ->
        let+ result = S.consume ~core_pred s args in
        match result with
        | Ok (s', args') -> Ok (SMap.add idx s' a, args')
        | Error e -> Error (InnerError (idx, e))

    (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
  let produce ~(core_pred:string) (a:t) (args:vt list) : t Delayed.t =
    let open Delayed.Syntax in
    match args with
    | [] -> Delayed.return a
    | idx :: args ->
      let idx = I.of_val idx in
      match SMap.find_opt idx a with
      | None -> Delayed.return a
      | Some s ->
        let+ s' = S.produce ~core_pred s args in
        SMap.add idx s' a

  let is_overlapping_asrt s = S.is_overlapping_asrt s

  let copy s = s

  let pp fmt s =
    let pp_pair fmt (idx, s) = Fmt.pf fmt "@[<h>%a -> %a@]" I.pp idx S.pp s in
    Fmt.pf fmt "@[<v 2>{%a}@]" (Fmt.iter_bindings SMap.iter pp_pair) s

  let substitution_in_place (sub:st) (s:t) : t Delayed.t =
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

  (* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
  let clean_up ?(keep=Expr.Set.empty) _ = failwith "Implement here (clean_up)"

  let lvars s =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.lvars s)) s empty

  let alocs s =
    let open Containers.SS in
    SMap.fold (fun _ s acc -> union acc (S.alocs s)) s empty

  (* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
  let assertions ?(to_keep=Containers.SS.empty) s = map_entries s (S.assertions ~to_keep) |> List.flatten

  let mem_constraints s = map_entries s S.mem_constraints |> List.flatten

  let pp_c_fix fmt f = match f with
    | FAddIndex idx -> Fmt.pf fmt "Missing index fix %a" I.pp idx
    | FInnerFix (i, e) -> Fmt.pf fmt "Inner fix: %a" S.pp_c_fix e

  let get_recovery_tactic (s:t) (e:err_t) = match e with
    | InnerError (idx, e) -> S.get_recovery_tactic (SMap.find idx s) e
    | _ -> failwith "Implement here (get_recovery_tactic)"

  let pp_err fmt e = Fmt.string fmt (show_err_t e)
  let get_failing_constraint e = match e with
  | InnerError (idx, e) -> S.get_failing_constraint e
  | _ -> failwith "Implement here (get_failing_constraint)"

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
  let pp_by_need _ = pp
  let get_print_info _ _ = (Containers.SS.empty, Containers.SS.empty)
  let sure_is_nonempty s = SMap.for_all (fun _ s -> S.sure_is_nonempty s) s

  let split_further s p ins e = match e with
    | InnerError (idx, e) -> S.split_further (SMap.find idx s) p ins e
    | _ -> failwith "Implement here (split_further)"

  module Lift = struct

    open Gillian.Debugger.Utils

    (* Refer to MonadicSMemory.mli *)

    let add_variables
      ~(store:(string * vt) list)
      ~(memory:t)
      ~(is_gil_file:'a)
      ~(get_new_scope_id:(unit -> int))
      (scopes:(int, Variable.t list) Hashtbl.t)
      : Variable.scope list =
      failwith "Implement here (add_variables)"

  end


end
