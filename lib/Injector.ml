open Gil_syntax
open Gillian.Monadic
open Delayed.Syntax
open Delayed_result.Syntax

(* TODO: If transformers get a nicer typing that exposes their internals better
   (actions, predicates and state type) injection hooks could be made type safe and maybe
   nice? for now this works though *)

type injection_hook = string -> Expr.t list -> Expr.t list Delayed.t

module type Injection = sig
  (** Called with the predicate's name and ins + outs before its production into the state. Replaces ins+outs *)
  val pre_produce : injection_hook

  (** Called with the predicate's name and ins before its consumption from the state. Replaces ins *)
  val pre_consume : injection_hook

  (** Called with the predicate's name and outs after its consumption from the state. Replaces outs *)
  val post_consume : injection_hook

  (** Called with the action's name and args before its execution. Replaces args *)
  val pre_execute_action : injection_hook

  (** Called with the action's name and returns after its execution. Replaces returns *)
  val post_execute_action : injection_hook
end

module Make (I : Injection) (S : MyMonadicSMemory.S) : MyMonadicSMemory.S =
struct
  include S

  let consume p s ins =
    let* ins' = I.pre_consume (pred_to_str p) ins in
    let** s', outs = consume p s ins' in
    let* outs' = I.post_consume (pred_to_str p) outs in
    Delayed_result.ok (s', outs')

  let produce p s insouts =
    let* insouts' = I.pre_produce (pred_to_str p) insouts in
    produce p s insouts'

  let execute_action a s args =
    let* args' = I.pre_execute_action (action_to_str a) args in
    let** s', returns = execute_action a s args' in
    let* returns' = I.post_execute_action (action_to_str a) returns in
    Delayed_result.ok (s', returns')
end
