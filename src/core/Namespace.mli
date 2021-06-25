type +'a t

val empty : 'a t

(** Associate a symbol with a possibly qualified identifier in a namespace. *)
val add : Ident.t -> 'a -> 'a t -> 'a t

(** Transform and add a namespace into another namespace. *)
val nest : unit Yuujinchou.Pattern.t -> 'a t -> 'a t -> 'a t

(** Look up the symbol associated with an possibly qualified identifier in a namespace. *)
val find : Ident.t -> 'a t -> 'a option
