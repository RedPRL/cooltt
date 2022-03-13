type path = Yuujinchou.Pattern.path

type +'a t
type 'a pattern = ([< `Print of string option ] as 'a) Yuujinchou.Pattern.t
type ('a, 'error) result = ('a, [> `BindingNotFound of path | `Shadowing of path ] as 'error) Stdlib.result

val empty : 'a t

val prefix : path -> 'a t -> 'a t

val transform : shadowing:bool -> pp:(Format.formatter -> 'a -> unit) -> _ pattern -> 'a t -> ('a t, 'error) result

val union : shadowing:bool -> 'a t -> 'a t -> ('a t, 'error) result

val add : shadowing:bool -> Ident.t -> 'a -> 'a t -> ('a t, 'error) result

val find : Ident.t -> 'a t -> 'a option
