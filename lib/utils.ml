open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

let rec override_preds id (pred: Asrt.t): Asrt.t = match pred with
| Star (p1, p2) -> Star (override_preds id p1, override_preds id p2)
| Pred (name, e) -> Pred (id ^ name, e)
| GA (name, ins, outs) -> GA (id ^ name, ins, outs)
| Wand ({ lhs = (lhs_name, lhs_e); rhs = (rhs_name, rhs_e) }) ->
  Wand { lhs = (id ^ lhs_name, lhs_e); rhs = (id ^ rhs_name, rhs_e) }
| _ -> pred
