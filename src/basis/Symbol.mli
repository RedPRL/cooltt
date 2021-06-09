(* FIXME: This is anti-modular, but it makes the symbol
   table code less janky for now.
 *)
type t = {gen : int; name : string option}

val fresh : unit -> t
val named : string -> t
val named_opt : string option -> t

val compare : t -> t -> int
val equal : t -> t -> bool

val pp : t Pp.printer
val show : t -> string
