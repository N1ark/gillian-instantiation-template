open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax
module DR = Delayed_result

type init_data = unit

type vt = Values.t

type st = Subst.t

type c_fix_t =
  | FAddState of vt
type err_t =
  | MissingState
  | DoubleAlloc
  | DoubleFree
[@@deriving show, yojson]

type t =
  | None
  | Val of Values.t
[@@deriving show, yojson]

type action_ret = (t * vt list, err_t) result


let pp_v v = Yojson.Safe.to_string (Values.to_yojson v)
let pp_t v = match v with
  | None -> "None"
  | Val v -> Printf.sprintf "Val(%s)" (pp_v v)


let init (i:init_data) : t = None
let get_init_data (i:t) : init_data = ()

let clear (v:t) : t =
  failwith "Implement here (clear)"

let execute_alloc v args = match v, args with
  | None, [v] -> Ok (Val v, [])
  | Val _, _ -> Error DoubleAlloc
  | _, _ -> failwith "Invalid alloc call"

let execute_free v args = match v, args with
  | None, _ -> Error DoubleFree
  | Val _, [] -> Ok (None, [])
  | _, _ -> failwith "Invalid free call"

let execute_load v args = match v, args with
  | None, _ -> Error MissingState
  | Val v, [] -> Ok (Val v, [v])
  | _, _ -> failwith "Invalid load call"

let execute_store v args = match v, args with
  | None, _ -> Error MissingState
  | Val v, [v'] -> Ok (Val v', [])
  | _, _ -> failwith "Invalid store call"

(* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
let execute_action ~(action_name:string) (v:t) (args:vt list) : action_ret Delayed.t =
  let res = match action_name with
    | "load" -> execute_load v args
    | "store" -> execute_store v args
    | "alloc" -> execute_alloc v args
    | "free" -> execute_free v args
    | _ -> failwith (Printf.sprintf "Unrecognized action: %s" action_name)
  in match res with
    | Ok (v', args') -> Delayed.return (Ok (v', args'))
    | Error e -> Delayed.return (Error e)

  (* val consume : core_pred:string -> t -> vt list -> action_ret Delayed.t *)
let consume ~(core_pred:string) (a:t) (args:vt list) : action_ret Delayed.t =
  failwith (Printf.sprintf "Implement here (consume %s)" core_pred)

  (* val produce : core_pred:string -> t -> vt list -> t Delayed.t*)
let produce ~(core_pred:string) (a:t) (args:vt list) : t Delayed.t =
  failwith (Printf.sprintf "Implement here (produce %s)" core_pred)

let is_overlapping_asrt _ = failwith "Implement here (is_overlapping_asrt)"

let copy v = v

let pp fmt s = Format.fprintf fmt "%s" (pp_t s)

(* val substitution_in_place : st -> t -> t Delayed.t *)
let substitution_in_place subst (heap:t) =
  let open Delayed.Syntax in
  match heap with
  | None -> Delayed.return None
  | Val v -> (
      let v' = Subst.subst_in_expr ~partial:true subst v in
      Delayed.return (Val v')
    )

(* val clean_up : ?keep:Expr.Set.t -> t -> Expr.Set.t * Expr.Set.t *)
let clean_up ?(keep=Expr.Set.empty) _ = failwith "Implement here (clean_up)"

let lvars s = match s with
  | None -> Containers.SS.empty
  | Val v -> Expr.lvars v
let alocs s = Containers.SS.empty

(* val assertions : ?to_keep:Containers.SS.t -> t -> Asrt.t list *)
let assertions ?(to_keep=Containers.SS.empty) _ = failwith "Implement here (assertions)"
let mem_constraints s = []
let pp_c_fix fmt _ = Format.fprintf fmt "fix"
let get_recovery_tactic _ _ = failwith "Implement here (get_recovery_tactic)"
let pp_err fmt e = Format.fprintf fmt "%s" (show_err_t e)
let get_failing_constraint e = failwith "Implement here (get_failing_constraint)"

(* (c_fix_t list * Formula.t list * (string * Type.t) list * Containers.SS.t)
list
*)

let fresh_name =
  let counter = ref 0 in
  fun () ->
    let n = !counter in
    counter := !counter + 1;
    Printf.sprintf "fresh_%d" n

let get_fixes s pfs tenv = function
| MissingState -> [
  ([FAddState (LVar (fresh_name ()))], [], [], Containers.SS.empty)
]
| _ -> []

let can_fix = function
| MissingState -> true
| _ -> false
let apply_fix s = function
| FAddState v -> DR.ok (Val v)
let pp_by_need _ = pp
let get_print_info _ _ = (Containers.SS.empty, Containers.SS.empty)
let sure_is_nonempty _ = false

let split_further _ _ _ _ = failwith "Implement here (split_further)"

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
