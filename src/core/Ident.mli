open Basis

module J = Ezjsonm

type t = [`Anon | `User of string list | `Machine of string | `Unfolder of t | `Blocked of t list]

(* Jon says: I do not like this type!  *)
type 'a some = 'a constraint 'a = [< t ]
type user = [ `User of string list ]

val user : string list -> t
val machine : string -> t
val unfolder : t -> t
val blocked : t list -> t
val anon : t

val pp : t Pp.printer
val pp_user : user Pp.printer
val to_string : t -> string
val to_string_opt : t -> string option

val user_to_string_opt : user -> string option

val json_of_ident : t -> J.value
val json_to_ident : J.value -> t
val json_of_user : [`User of string list ] -> [> `A of J.value list ]
val json_to_user : J.value -> [`User of string list]

val equal : t -> t -> bool
