open Basis

type t

val empty : t

(** Associate a symbol with a possibly qualified identifier in a namespace. *)
val add_symbol : Ident.t -> Symbol.t -> t -> t

(** Nest a namespace inside of another namespace under a qualified path. *)
val add_namespace : string list -> t -> t -> t

(** Look up the symbol associated with an possibly qualified identifier in a namespace. *)
val resolve_symbol : Ident.t -> t -> Symbol.t option
