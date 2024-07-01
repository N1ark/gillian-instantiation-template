open Utils
open Gil_syntax
module BlockTree = C_states.BlockTree.M
module Delayed = Gillian.Monadic.Delayed
module DR = Gillian.Monadic.Delayed_result

(* Base construct *)
module BaseMemory = PMap (LocationIndex) (Freeable (BlockTree))

(* Move action implementation *)
module MovableMap : MyMonadicSMemory with type t = BaseMemory.t = struct
  include BaseMemory

  type action = Base of BaseMemory.action | Move

  let action_to_str = function
    | Base a -> action_to_str a
    | Move -> "mem_move"

  let action_from_str = function
    | "mem_move" -> Some Move
    | str -> Option.map (fun a -> Base a) (action_from_str str)

  let list_actions () =
    List.map (fun (a, args, ret) -> (Base a, args, ret)) (list_actions ())
    @ [ (Move, [], []) ]

  let exec_move s args =
    match args with
    | [ dst_loc; dst_ofs; src_loc; src_ofs; size ] -> (
        let open DR.Syntax in
        let open Formula.Infix in
        if%sat size #== (Expr.int 0) then DR.ok (s, [])
        else
          let h, d = s in
          let** h, _, src = validate_index (h, d) src_loc in
          let** h, dest_idx, dest = validate_index (h, d) dst_loc in
          match (src, dest) with
          | States.Freeable.None, _ -> DR.error (MissingCell src_loc)
          | _, States.Freeable.None -> DR.error (MissingCell dst_loc)
          | States.Freeable.Freed, _ | _, States.Freeable.Freed ->
              failwith "Tried moving freed state"
          | States.Freeable.SubState src, States.Freeable.SubState dest ->
              let** dest =
                DR.map_error (BlockTree.move dest dst_ofs src src_ofs size)
                  (fun _ -> failwith "")
              in
              let s' =
                update_entry (h, d) dest_idx (States.Freeable.SubState dest)
              in
              DR.ok (s', []))
    | _ -> failwith "Invalid arguments for mem_move"

  let execute_action action s args =
    match action with
    | Base a -> execute_action a s args
    | Move -> exec_move s args
end

(* Mappings etc *)
module CSubst : NameMap = struct
  let action_substitutions = [ ("mem_alloc", "alloc"); ("mem_free", "free") ]
  let pred_substitutions = [ ("mem_freed", "freed") ]
end

module ArgRelocateInjection : Injection with type t = MovableMap.t = struct
  include DummyInject (MovableMap)

  let pre_execute_action action (s, args) =
    match (action, args) with
    | "mem_load", c :: loc :: rest | "mem_store", c :: loc :: rest ->
        Delayed.return (s, loc :: c :: rest)
    | _, _ -> Delayed.return (s, args)
end

module ParserAndCompiler = ParserAndCompiler.Dummy

module ExternalSemantics =
  Gillian.General.External.Dummy (ParserAndCompiler.Annot)

module MonadicSMemory =
  Injector (ArgRelocateInjection) (Mapper (CSubst) (MovableMap))
