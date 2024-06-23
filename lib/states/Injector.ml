open Gil_syntax
open Gillian.Monadic
open Delayed.Syntax
open Delayed_result.Syntax

(* TODO: If transformers get a nicer typing that exposes their internals better
   (actions, predicates) injection hooks could be made type safe and maybe
   nice? for now this works though *)

type 'a injection_hook = string -> 'a -> 'a Delayed.t

module type Injection = sig
  type t

  (** Called with the predicate's name and ins + outs before its production into the state. Replaces ins+outs *)
  val pre_produce : (t * Expr.t list) injection_hook

  (** Called with the predicate's name and ins before its consumption from the state. Replaces ins *)
  val pre_consume : (t * Expr.t list) injection_hook

  (** Called with the predicate's name and outs after its consumption from the state. Replaces outs *)
  val post_consume : (t * Expr.t list) injection_hook

  (** Called with the action's name and args before its execution. Replaces args *)
  val pre_execute_action : (t * Expr.t list) injection_hook

  (** Called with the action's name and returns after its execution. Replaces returns *)
  val post_execute_action : (t * Expr.t list) injection_hook
end

module Make (I : Injection) (S : MyMonadicSMemory.S with type t = I.t) :
  MyMonadicSMemory.S with type t = S.t = struct
  include S

  let consume p s ins =
    let p_str = pred_to_str p in
    let* s', ins' = I.pre_consume p_str (s, ins) in
    let** s'', outs = consume p s' ins' in
    let* s''', outs' = I.post_consume p_str (s'', outs) in
    Delayed_result.ok (s''', outs')

  let produce p s insouts =
    let p_str = pred_to_str p in
    let* s', insouts' = I.pre_produce p_str (s, insouts) in
    produce p s' insouts'

  let execute_action a s args =
    let a_str = action_to_str a in
    let* s', args' = I.pre_execute_action a_str (s, args) in
    let** s'', returns = execute_action a s' args' in
    let* s''', returns' = I.post_execute_action a_str (s'', returns) in
    Delayed_result.ok (s''', returns')
end
