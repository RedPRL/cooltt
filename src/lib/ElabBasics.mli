module CS := ConcreteSyntax
module D := Domain
module S := Syntax

open CoolBasis
open Bwd

include module type of Monads.ElabM

val push_problem : string -> 'a m -> 'a m
val problem : string bwd m

val elab_err : ElabError.t -> 'a m

val update_span : LexingUtil.span option -> 'a m -> 'a m
val abstract : Ident.t -> D.tp -> (D.con -> 'a m) -> 'a m

val add_global : Ident.t -> D.tp -> D.con option -> Symbol.t m
val add_flex_global : D.tp -> Symbol.t m

val resolve : Ident.t -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> (D.tp * D.con option) m
val get_local_tp : int -> D.tp m
val get_local : int -> D.con m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.con -> D.con -> unit m

val dest_pi : D.tp -> (D.tp * D.tp_clo) m
val dest_sg : D.tp -> (D.tp * D.tp_clo) m

val with_pp : (Pp.env -> 'a m) -> 'a m

val expected_connective : ElabError.connective -> D.tp -> 'a m
