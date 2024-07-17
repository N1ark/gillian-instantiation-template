open Utils
open Gil_syntax
module BlockTree = C_states.BlockTree.M
module Delayed = Gillian.Monadic.Delayed
module DR = Gillian.Monadic.Delayed_result

(* Base construct + Move action implementation *)
module BaseMemory = struct
  module BaseMemory = PMap (LocationIndex) (Freeable (BlockTree))
  include BaseMemory

  type action = Base of BaseMemory.action | Move | SetZeros

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
          let h, d = s in
          let** h, src_loc', src = validate_index (h, d) src_loc in
          let** h, dst_loc', dest = validate_index (h, d) dst_loc in
          match (src, dest) with
          (* TODO: proper miss errors here *)
          | States.Freeable.None, _ -> DR.error (NotAllocated src_loc')
          | _, States.Freeable.None -> DR.error (NotAllocated dst_loc')
          | States.Freeable.Freed, _ | _, States.Freeable.Freed ->
              failwith "Tried moving freed state"
          | States.Freeable.SubState src, States.Freeable.SubState dest ->
              let** dest =
                DR.map_error (BlockTree.move dest dst_ofs src src_ofs size)
                  (fun _ -> failwith "")
              in
              let s' =
                update_entry (h, d) dst_loc dst_loc'
                  (States.Freeable.SubState dest)
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

(* ALoc optim + Move action implementation *)
module ALocMemory = struct
  module BaseMemory = ALocPMap (Freeable (BlockTree))
  include BaseMemory

  type action = Base of BaseMemory.action | Move | SetZeros

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
          let** src_loc', src = validate_index s src_loc in
          let** dst_loc', dest = validate_index s dst_loc in
          match (src, dest) with
          (* TODO: proper miss errors here *)
          | States.Freeable.None, _ -> DR.error (NotAllocated src_loc')
          | _, States.Freeable.None -> DR.error (NotAllocated dst_loc')
          | States.Freeable.Freed, _ | _, States.Freeable.Freed ->
              failwith "Tried moving freed state"
          | States.Freeable.SubState src, States.Freeable.SubState dest ->
              let** dest =
                DR.map_error (BlockTree.move dest dst_ofs src src_ofs size)
                  (fun _ -> failwith "")
              in
              let s' =
                update_entry s dst_loc' (States.Freeable.SubState dest)
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

(* ALoc optim + Move action implementation *)
module SplitMemory = struct
  module BaseMemory = SplitPMap (LocationIndex) (Freeable (BlockTree))
  include BaseMemory

  type action = Base of BaseMemory.action | Move | SetZeros

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
          let** src_loc', src = validate_index s src_loc in
          let** dst_loc', dest = validate_index s dst_loc in
          match (src, dest) with
          (* TODO: proper miss errors here *)
          | States.Freeable.None, _ -> DR.error (NotAllocated src_loc')
          | _, States.Freeable.None -> DR.error (NotAllocated dst_loc')
          | States.Freeable.Freed, _ | _, States.Freeable.Freed ->
              failwith "Tried moving freed state"
          | States.Freeable.SubState src, States.Freeable.SubState dest ->
              let** dest =
                DR.map_error (BlockTree.move dest dst_ofs src src_ofs size)
                  (fun _ -> failwith "")
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

module Wrap (S : MyMonadicSMemory) =
  Injector (ArgRelocateInjection (S)) (Mapper (CSubst) (S))

module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module MonadicSMemory_Base = Wrap (BaseMemory)
module MonadicSMemory_ALoc = Wrap (ALocMemory)
module MonadicSMemory_Split = Wrap (SplitMemory)
