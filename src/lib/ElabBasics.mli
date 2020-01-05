module CS := ConcreteSyntax
module D := Domain
module S := Syntax

include module type of Monads.ElabM

val elab_err : ElabError.t -> 'a m

val push_var : CS.ident option -> D.tp -> 'a m -> 'a m
val add_global : CS.ident option -> D.tp -> D.t option -> Symbol.t m

val resolve : CS.ident -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> D.nf m
val get_local_tp : int -> D.tp m
val get_local : int -> D.t m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.t -> D.t -> unit m

open TLNat
val dest_pi : D.tp -> (D.tp * ze su D.tp_clo) m
val dest_sg : D.tp -> (D.tp * ze su D.tp_clo) m
val dest_id : D.tp -> (D.tp * D.t * D.t) m