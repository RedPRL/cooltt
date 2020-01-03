type t

val fresh : unit -> t
val named : string -> t
val named_opt : string option -> t

val compare : t -> t -> int
val equal : t -> t -> bool

val pp : Format.formatter -> t -> unit
val show : t -> string