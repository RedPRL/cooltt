module CS := ConcreteSyntax
module D := Domain
module S := Syntax

open CoolBasis.Bwd

include module type of Monads.ElabM

val push_problem : string -> 'a m -> 'a m
val problem : string bwd m
val current_ghost : S.ghost option m

val elab_err : ElabError.t -> 'a m

val push_var : CS.ident option -> D.tp -> 'a m -> 'a m
val push_def : CS.ident option -> D.tp -> D.con -> 'a m -> 'a m

val abstract : CS.ident option -> D.tp -> (D.con -> 'a m) -> 'a m
val define : CS.ident option -> D.tp -> D.con -> (D.con -> 'a m) -> 'a m

val add_global : CS.ident option -> D.tp -> D.con option -> Symbol.t m
val add_flex_global : D.tp -> Symbol.t m

val resolve : CS.ident -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> (D.tp * D.con) m
val get_local_tp : int -> D.tp m
val get_local : int -> D.con m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.con -> D.con -> unit m

open CoolBasis.TLNat
val dest_pi : D.tp -> (D.tp * ze su D.tp_clo) m
val dest_sg : D.tp -> (D.tp * ze su D.tp_clo) m
val dest_id : D.tp -> (D.tp * D.con * D.con) m