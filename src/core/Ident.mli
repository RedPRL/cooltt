open Basis
open NonEmpty

(* FIXME: Is the non_empty pulling it's weight here? *)
type t = [`Anon | `Unqual of string | `Qual of string non_empty * string | `Machine of string]

val to_string : t -> string
val pp : t Pp.printer
val pp_name : t -> string option
