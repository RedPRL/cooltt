module CS := ConcreteSyntax
module D := Domain
module S := Syntax

type 'a m := 'a ElabMonad.m

val push_var : CS.ident option -> D.tp -> 'a m -> 'a m
val add_global : CS.ident option -> D.tp -> D.t option -> Symbol.t m

val resolve : CS.ident -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> D.nf m
val get_local_tp : int -> D.tp m
val get_local : int -> D.t m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.t -> D.t -> unit m

val dest_pi : D.tp -> (D.tp * (S.tp, D.tp) D.clo) m