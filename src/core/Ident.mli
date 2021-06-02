open Basis

type t = [`Anon | `Unqual of string | `Qual of string list * string | `Machine of string]

val to_string : t -> string
val pp : t Pp.printer
val pp_name : t -> string option
