open Basis

type t = [`Anon | `User of string list | `Machine of string]

val pp : t Pp.printer
val to_string : t -> string
val to_string_opt : t -> string option

val equal : t -> t -> bool
