open CoolBasis

type 'a cof = 
  | Eq of 'a * 'a
  | Join of 'a cof * 'a cof
  | Meet of 'a cof * 'a cof
  | Bot
  | Top

type ('a, 'b) tree =
  | Const of 'a cof * 'b
  | Split of ('a, 'b) tree * ('a, 'b) tree
  | Abort


val eq : 'a -> 'a -> 'a cof
val join : 'a cof -> 'a cof -> 'a cof
val meet : 'a cof -> 'a cof -> 'a cof
val bot : 'a cof
val top : 'a cof

val const : 'a cof -> 'b -> ('a, 'b) tree
val split : ('a, 'b) tree -> ('a, 'b) tree -> ('a, 'b) tree
val abort : ('a, 'b) tree


val condition : ('a, 'b) tree -> 'a cof


val pp_cof 
  : (Pp.env -> 'a Pp.printer) 
  -> Pp.env 
  -> 'a cof Pp.printer

val pp_tree 
  : (Pp.env -> 'a Pp.printer)
  -> (Pp.env -> 'b Pp.printer)
  -> Pp.env -> ('a, 'b) tree Pp.printer