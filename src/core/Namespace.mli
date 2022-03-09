type +'a t
type 'a pattern = ([< `Print of string option] as 'a) Yuujinchou.Pattern.t
type ('a, 'error) result = ('a, [> `BindingNotFound of string list | `Shadowing of string list ] as 'error) Stdlib.result

val empty : 'a t

val transform : shadowing:bool -> pp:(Format.formatter -> 'a -> unit) -> 'b pattern -> 'a t -> ('a t, 'error) result

val union : shadowing:bool -> 'a t -> 'a t -> ('a t, 'error) result

val add : shadowing:bool -> Ident.t -> 'a -> 'a t -> ('a t, 'error) result

val find : Ident.t -> 'a t -> 'a option
