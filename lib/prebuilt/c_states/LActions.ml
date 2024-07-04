(* First, type definitions *)

type ac = DropPerm | GetCurPerm | WeakValidPointer | Store | Load
type ga = Single | Array | Hole | Zeros | Bounds

let str_ac = function
  | DropPerm -> "mem_dropperm"
  | WeakValidPointer -> "mem_weakvalidpointer"
  | GetCurPerm -> "mem_getperm"
  | Store -> "mem_store"
  | Load -> "mem_load"

let ac_from_str = function
  | "mem_dropperm" -> DropPerm
  | "mem_weakvalidpointer" -> WeakValidPointer
  | "mem_getcurperm" -> GetCurPerm
  | "mem_store" -> Store
  | "mem_load" -> Load
  | _ -> failwith "Unrecognized action"

let str_ga = function
  | Single -> "mem_single"
  | Array -> "mem_array"
  | Hole -> "mem_hole"
  | Zeros -> "mem_zeros"
  | Bounds -> "mem_bounds"

let ga_from_str = function
  | "mem_single" -> Single
  | "mem_array" -> Array
  | "mem_bounds" -> Bounds
  | "mem_zeros" -> Zeros
  | "mem_hole" -> Hole
  | _ -> failwith "Unrecognized predicate"
