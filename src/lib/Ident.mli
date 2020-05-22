open CoolBasis

type t = [`Anon | `User of string | `Machine of string]

val to_string : t -> string
val pp : t Pp.printer
