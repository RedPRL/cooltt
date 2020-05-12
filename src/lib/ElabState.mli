open CoolBasis

module D := Domain
module CS := ConcreteSyntax

type t

val init : t
val add_global : Ident.t -> D.tp -> D.con option -> t -> Symbol.t * t
val add_flex_global : D.tp -> t -> Symbol.t * t
val resolve_global : Ident.t -> t -> Symbol.t option

val get_global : Symbol.t -> t -> D.tp * D.con option
val get_flexity : Symbol.t -> t -> [`Flex | `Rigid]
