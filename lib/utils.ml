open Gillian.Utils
open Gillian.Monadic
open Gillian.Symbolic
open Gil_syntax

let rec override_preds id (pred: Asrt.t): Asrt.t = match pred with
| Star (p1, p2) -> Star (override_preds id p1, override_preds id p2)
| GA (name, ins, outs) -> GA (id ^ name, ins, outs)
| _ -> pred

let split_str s = match String.length s with
  | 0 -> None
  | n -> Some (String.sub s 0 1, String.sub s 1 (n - 1))
