open Basis

module D = Domain

(** Some metadata about a given code unit. *)
type t

type symbol = Symbol.t

(** Return the name of the code unit that a symbol originated from. *)
val origin : symbol -> string

(** The name of a given code unit *)
val name : t -> string

(** All of the code unit this unit directly imports. *)
val imports : t -> string list

(** Create a code unit. *)
val create : string -> t

(** Add a binding to a given code unit. *)
val add_global : Ident.t -> D.tp -> D.con option -> t -> (symbol * t)

(** Attempt to resolve an identifier a given code unit. *)
val resolve_global : Ident.t -> t -> symbol option

(** Get the binding associated with a symbol. *)
val get_global : symbol -> t -> D.tp * D.con option

(** Add another code unit as an import. *)
val add_import : string list -> t -> t -> t
