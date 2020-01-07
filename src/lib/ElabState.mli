module D := Domain
module CS := ConcreteSyntax

type t

val init : t
val add_global : CS.ident option -> D.tp -> D.con option -> t -> Symbol.t * t
val resolve_global : CS.ident -> t -> Symbol.t option
val get_global : Symbol.t -> t -> D.nf