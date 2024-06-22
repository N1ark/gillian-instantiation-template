open Gillian.Concrete
module Literal = Gillian.Gil_syntax.Literal
module Expr = Gillian.Gil_syntax.Expr

type vt = Values.t

type st = Subst.t
type err_t = unit [@@deriving show]

type t = unit

type init_data = unit

let init () = ()

let copy () = ()
type action_ret = (t * vt list, err_t) result


(* val execute_action : action_name:string -> t -> vt list -> action_ret Delayed.t*)
let execute_action (action_name:string) (_:t) (_:vt list) : action_ret =
  failwith (Printf.sprintf "Implement here (CMem.execute_action %s)" action_name)

let pp _ _ = ()

let pp_err _ _ = ()
