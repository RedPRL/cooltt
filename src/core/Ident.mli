open Basis

type t = [`Anon | `User of string list * string | `Machine of string]

val pp : t Pp.printer
val to_string : t -> string
val to_string_opt : t -> string option
