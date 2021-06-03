open Basis

module D := Domain

type t

val init : t
val add_global : Ident.t -> D.tp -> D.con option -> t -> Symbol.t * t
val resolve_global : Ident.t -> t -> Symbol.t option

val add_namespace : string list -> Namespace.t -> t -> t

val get_global : Symbol.t -> t -> D.tp * D.con option
