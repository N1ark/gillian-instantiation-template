type ('a, 'e, 'm) sym_result = Ok of 'a | LFail of 'e | Miss of 'm
type ('a, 'e, 'm) t = ('a, 'e, 'm) sym_result

let map f = function
  | Ok x -> Ok (f x)
  | LFail e -> LFail e
  | Miss m -> Miss m

let bind x f =
  match x with
  | Ok x -> f x
  | LFail e -> LFail e
  | Miss m -> Miss m

let ok x = Ok x
let lfail e = LFail e
let miss m = Miss m
