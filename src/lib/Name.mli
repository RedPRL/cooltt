include Map.OrderedType

val set_debug_mode : bool -> unit

val named : string option -> t
val fresh : unit -> t

val to_string : t -> string
val name : t -> string option

val pp : t Pp.t0
