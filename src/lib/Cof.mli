type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a list
  | Meet of 'a list

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v


val var : 'v -> ('a, 'v) cof
val eq : 'a -> 'a -> ('a, 'v) cof
val join : ('a, 'v) cof list -> ('a, 'v) cof
val meet : ('a, 'v) cof list -> ('a, 'v) cof
val bot : ('a, 'v) cof
val top : ('a, 'v) cof

val boundary : Dim.dim -> (Dim.dim, 'v) cof

val reduce : ('a, 'v) cof -> ('a, 'v) cof
