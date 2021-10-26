open Basis

type t = [`Anon | `User of string list | `Machine of string]
type 'a some = 'a constraint 'a = [< t ]
type user = [ `User of string list ]

val user : string list -> t

val pp : t Pp.printer
val pp_user : user Pp.printer
val to_string : t -> string
val to_string_opt : t -> string option

val user_to_string_opt : user -> string option

val equal : user -> user -> bool
