open CoolBasis

type t = [`Anon | `User of string | `Machine of string]

val pp : t Pp.printer
