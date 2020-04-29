open CoolBasis

type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a * 'a
  | Meet of 'a * 'a
  | Bot
  | Top

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v


val var : 'v -> ('a, 'v) cof
val eq : 'a -> 'a -> ('a, 'v) cof
val join : ('a, 'v) cof -> ('a, 'v) cof -> ('a, 'v) cof
val meet : ('a, 'v) cof -> ('a, 'v) cof -> ('a, 'v) cof
val bot : ('a, 'v) cof
val top : ('a, 'v) cof

val reduce : ('a, 'v) cof -> ('a, 'v) cof

val pp_cof
  : (Pp.env -> 'v Pp.printer)
  -> (Pp.env -> 'a Pp.printer)
  -> Pp.env
  -> ('a, 'v) cof Pp.printer
