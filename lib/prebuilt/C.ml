open Utils
open Gil_syntax
module BlockTree = C_states.BlockTree.M
module Delayed = Gillian.Monadic.Delayed
module DR = Gillian.Monadic.Delayed_result

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
    | Move -> "mem_move"
    | SetZeros -> "mem_setZeros"

  let action_from_str = function
    | "mem_move" -> Some Move
    | "mem_setZeros" -> Some SetZeros
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
    let pred = pred_from_str "mem_zeros" in
    let pred = Option.get pred in
    let s' = produce pred s args in
    Delayed.map s' (fun s' -> Ok (s', []))

  let execute_action action s args =
    match action with
    | Base a -> execute_action a s args
    | Move -> exec_move s args
    | SetZeros -> exec_set_zeros s args
end

(* Mappings etc *)
module CSubst : NameMap = struct
  let action_substitutions = [ ("mem_alloc", "alloc"); ("mem_free", "free") ]
  let pred_substitutions = [ ("mem_freed", "freed") ]
end

module ArgRelocateInjection (S : MyMonadicSMemory) = struct
  include DummyInject (S)

  let pre_execute_action action (s, args) =
    match (action, args) with
    | "mem_load", c :: loc :: rest | "mem_store", c :: loc :: rest ->
        Delayed.return (s, loc :: c :: rest)
    | _, _ -> Delayed.return (s, args)

  let post_execute_action action (s, a, r) =
    match action with
    | "mem_dropperm"
    | "mem_weakvalidpointer"
    | "mem_getcurperm"
    | "mem_store"
    | "mem_load" -> (
        match r with
        (* C doesn't need returned index *)
        | _ :: rest -> Delayed.return (s, a, rest)
        | _ -> Delayed.return (s, a, r))
    | _ -> Delayed.return (s, a, r)
end

module Wrap (S : C_PMapType) = struct
  module Intermediary = ExtendMemory (S)

  include
    Injector
      (ArgRelocateInjection (Intermediary)) (Mapper (CSubst) (Intermediary))
end

module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module MonadicSMemory_Base = Wrap (BaseMemory)
module MonadicSMemory_ALoc = Wrap (ALocMemory)
module MonadicSMemory_Split = Wrap (SplitMemory)
