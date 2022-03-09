type zero
type !'a succ

type ('a, _) t =
  | Nil : ('a, zero) t
  | Cons : 'a * ('a, 'd) t -> ('a, 'd succ) t

let rec length : type d . ('a, d) t -> int =
  function Nil -> 0 | Cons (_, xs) -> length xs
let cons x xs = Cons (x, xs)
let uncons : ('a, 'd succ) t -> 'a * ('a, 'd) t =
  function Cons (x, xs) -> x, xs
let hd : ('a, 'd succ) t -> 'a = function Cons (x, _) -> x
let tl : ('a, 'd succ) t -> ('a, 'd) t = function Cons (_, xs) -> xs
let rec map : type d . f:('a -> 'b) -> ('a, d) t -> ('b, d) t =
  fun ~f ->
  function
  | Nil -> Nil
  | Cons (x, xs) -> Cons (f x, map ~f xs)
