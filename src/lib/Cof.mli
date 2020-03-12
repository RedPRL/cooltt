open CoolBasis

type ('r, 'a) cof_f = 
  | Eq of 'r * 'r
  | Join of 'a * 'a 
  | Meet of 'a * 'a
  | Bot 
  | Top

type ('v, 'r) cof = 
  | Cof of ('r, ('v, 'r) cof) cof_f
  | Var of 'v

val var : 'v -> ('v, 'a) cof
val eq : 'a -> 'a -> ('v, 'a) cof
val join : ('v, 'a) cof -> ('v, 'a) cof -> ('v, 'a) cof
val meet : ('v, 'a) cof -> ('v, 'a) cof -> ('v, 'a) cof
val bot : ('v, 'a) cof
val top : ('v, 'a) cof

val reduce : ('v, 'a) cof -> ('v, 'a) cof

val pp_cof 
  : (Pp.env -> 'v Pp.printer) 
  -> (Pp.env -> 'a Pp.printer) 
  -> Pp.env 
  -> ('v, 'a) cof Pp.printer