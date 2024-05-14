open Gillian.Monadic
open SymResult

type ('a, 'e, 'm) t = ('a, 'e, 'm) sym_result Delayed.t

let ok ?learned x = Delayed.return ?learned (SymResult.ok x)
let lfail ?learned x = Delayed.return ?learned (SymResult.lfail x)
let miss ?learned x = Delayed.return ?learned (SymResult.miss x)
let of_result = Delayed.return

let map (x : ('a, 'e, 'm) t) (f : 'a -> 'b) : ('b, 'e, 'm) t =
  Delayed.map x (fun z -> SymResult.map f z)

let bind (x : ('a, 'e, 'm) t) (f : 'a -> ('b, 'e, 'm) t) : ('b, 'e, 'm) t =
  Delayed.bind x (function
    | Ok x -> f x
    | LFail z -> Delayed.return (LFail z)
    | Miss m -> Delayed.return (Miss m))

let map_bind (x : ('a, 'e, 'm) t) (f : 'a -> ('b, 'e, 'm) sym_result) :
    ('b, 'e, 'm) t =
  Delayed.map x (fun z -> SymResult.bind z f)

let bind_vanish_on_err (x : ('a, 'e, 'm) t) (f : 'a -> 'b Delayed.t) :
    'b Delayed.t =
  let open Delayed.Syntax in
  let* x = x in
  match x with
  | Ok x -> f x
  | LFail _ -> Delayed.vanish ()
  | Miss _ -> Delayed.vanish ()

module Syntax = struct
  let ( let** ) = bind
  let ( let++ ) = map
  let ( let+* ) = map_bind
  let ( let*? ) = bind_vanish_on_err
end
