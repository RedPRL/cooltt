module CS := ConcreteSyntax
module D := Domain
module S := Syntax

open Basis
open Bwd

include module type of Monads.ElabM

val push_problem : string -> 'a m -> 'a m
val problem : string bwd m

val elab_err : ElabError.t -> 'a m

val update_span : LexingUtil.span option -> 'a m -> 'a m
val abstract : Ident.t -> D.tp -> (D.con -> 'a m) -> 'a m

val add_global : Ident.t -> D.tp -> D.con option -> Symbol.t m

val resolve : Ident.t -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> (D.tp * D.con option) m
val get_local_tp : int -> D.tp m
val get_local : int -> D.con m

val quote_con : D.tp -> D.con -> S.t m
val quote_tp : D.tp -> S.tp m
val quote_cut : D.cut -> S.t m
val quote_cof : D.cof -> S.t m
val quote_dim : D.dim -> S.t m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.con -> D.con -> unit m

val with_pp : (Pp.env -> 'a m) -> 'a m

val expected_connective : ElabError.connective -> D.tp -> 'a m
