include module type of ConcreteSyntaxData

val show : t -> string

val pp_ident : Format.formatter -> ident -> unit

val pp : Format.formatter -> t -> unit