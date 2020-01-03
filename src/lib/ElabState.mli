module D := Domain
module CS := ConcreteSyntax

type t

val init : t
val add_global : CS.ident -> D.tp -> D.t -> t -> t
val resolve_global : CS.ident -> t -> Symbol.t option
val get_global : Symbol.t -> t -> D.nf