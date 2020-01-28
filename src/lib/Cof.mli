open CoolBasis

type ('v, 'a) cof = 
  | Var of 'v
  | Eq of 'a * 'a
  | Join of ('v, 'a) cof * ('v, 'a) cof
  | Meet of ('v, 'a) cof * ('v, 'a) cof
  | Bot
  | Top

type ('v, 'a, 'b) tree =
  | Const of ('v, 'a) cof * 'b
  | Split of ('v, 'a, 'b) tree * ('v, 'a, 'b) tree
  | Abort

val var : 'v -> ('v, 'a) cof
val eq : 'a -> 'a -> ('v, 'a) cof
val join : ('v, 'a) cof -> ('v, 'a) cof -> ('v, 'a) cof
val meet : ('v, 'a) cof -> ('v, 'a) cof -> ('v, 'a) cof
val bot : ('v, 'a) cof
val top : ('v, 'a) cof

val reduce : ('v, 'a) cof -> ('v, 'a) cof

val const : ('v, 'a) cof -> 'b -> ('v, 'a, 'b) tree
val split : ('v, 'a, 'b) tree -> ('v, 'a, 'b) tree -> ('v, 'a, 'b) tree
val abort : ('v, 'a, 'b) tree


val condition : ('v, 'a, 'b) tree -> ('v, 'a) cof


val pp_cof 
  : (Pp.env -> 'v Pp.printer) 
  -> (Pp.env -> 'a Pp.printer) 
  -> Pp.env 
  -> ('v, 'a) cof Pp.printer

val pp_tree 
  : (Pp.env -> 'v Pp.printer)
  -> (Pp.env -> 'a Pp.printer)
  -> (Pp.env -> 'b Pp.printer)
  -> Pp.env -> ('v, 'a, 'b) tree Pp.printer