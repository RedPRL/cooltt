type zero
type !'a succ
type (+'a, _) t =
  | Nil : ('a, zero) t
  | Cons : 'a * ('a, 'd) t -> ('a, 'd succ) t

val length : ('a, 'd) t -> int
val cons : 'a -> ('a, 'd) t -> ('a, 'd succ) t
val uncons : ('a, 'd succ) t -> 'a * ('a, 'd) t
val hd : ('a, 'd succ) t -> 'a
val tl : ('a, 'd succ) t -> ('a, 'd) t
val map : f:('a -> 'b) -> ('a, 'd) t -> ('b, 'd) t
