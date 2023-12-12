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

let execute_action _ _ _ = failwith "Implement here"

let pp _ _ = ()

let pp_err _ _ = ()