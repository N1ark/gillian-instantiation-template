open Utils
open Gil_syntax
module Delayed = Gillian.Monadic.Delayed
module DR = Gillian.Monadic.Delayed_result
module Global_env = Cgil_lib.Global_env

(* Import C-specific constructs *)
module BlockTree = C_states.BlockTree.M
module CGEnv = C_states.CGEnv.M

(* Base memories *)
module BaseBlock = Freeable (BlockTree)

module type C_PMapType = States.PMap.PMapType with type entry = BaseBlock.t

module BaseMemory : C_PMapType = PMap (LocationIndex) (BaseBlock)
module SplitMemory : C_PMapType = SplitPMap (LocationIndex) (BaseBlock)
module ALocMemory : C_PMapType = ALocPMap (BaseBlock)

(* Add move action implementation *)
module ExtendMemory (S : C_PMapType) = struct
  include S

  type action = Base of S.action | Move | SetZeros

  let action_to_str = function
    | Base a -> action_to_str a
    | Move -> "move"
    | SetZeros -> "setZeros"

  let action_from_str = function
    | "move" -> Some Move
    | "setZeros" -> Some SetZeros
    | str -> Option.map (fun a -> Base a) (action_from_str str)

  let list_actions () =
    List.map (fun (a, args, ret) -> (Base a, args, ret)) (list_actions ())
    @ [ (Move, [ "?" ], [ "?" ]) ]
    @ [ (SetZeros, [ "?" ], [ "?" ]) ]

  let exec_move s args =
    match args with
    | [ dst_loc; dst_ofs; src_loc; src_ofs; size ] -> (
        let open DR.Syntax in
        let open Formula.Infix in
        if%sat size #== (Expr.int 0) then DR.ok (s, [])
        else
          let** _, src = validate_index s src_loc in
          let** dst_loc', dest = validate_index s dst_loc in
          match (src, dest) with
          (* TODO: proper miss errors here *)
          | States.Freeable.None, _ | _, States.Freeable.None ->
              failwith
                "Tried moving from missing memory (no error handles this yet)"
          | States.Freeable.Freed, _ | _, States.Freeable.Freed ->
              failwith
                "Tried moving from freed memory (no error handles this yet)"
          | States.Freeable.SubState src, States.Freeable.SubState dest ->
              let** dest =
                DR.map_error (BlockTree.move dest dst_ofs src src_ofs size)
                  (fun _ ->
                    failwith
                      "Sub error when moving state (no error handles this yet)")
              in
              let s' =
                update_entry s dst_loc dst_loc' (States.Freeable.SubState dest)
              in
              DR.ok (s', []))
    | _ -> failwith "Invalid arguments for mem_move"

  let exec_set_zeros s args =
    let pred = pred_from_str "zeros" in
    let pred = Option.get pred in
    let s' = produce pred s args in
    Delayed.map s' (fun s' -> Ok (s', []))

  let execute_action action s args =
    match action with
    | Base a -> (
        let open Delayed.Syntax in
        let action = S.action_to_str a in
        let args =
          (* Move index to be the first argument *)
          match (action, args) with
          | "load", c :: loc :: rest | "store", c :: loc :: rest ->
              loc :: c :: rest
          | _ -> args
        in
        let+ r = execute_action a s args in
        match (action, r) with
        (* remove returned index (not needed in C) *)
        | "alloc", r -> r
        | _, Ok (s', _ :: rest) -> Ok (s', rest)
        | _, r -> r)
    | Move -> exec_move s args
    | SetZeros -> exec_set_zeros s args
end

module Wrap (S : C_PMapType) = struct
  module CMapMemory = ExtendMemory (S)

  module StateWithGEnv =
    Product
      (struct
        let id1 = "mem_"
        let id2 = "genv_"
      end)
      (CMapMemory)
      (CGEnv)

  include StateWithGEnv

  let pp f (s1, _) = CMapMemory.pp f s1
end

module MonadicSMemory_Base = Wrap (BaseMemory)
module MonadicSMemory_ALoc = Wrap (ALocMemory)
module MonadicSMemory_Split = Wrap (SplitMemory)
module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module InitData = Cgil_lib.Global_env
