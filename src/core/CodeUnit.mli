open Basis

module Global : Symbol.S

module Domain : module type of Domain.Make(Global)
module Syntax : module type of Syntax.Make(Global)

module CodeUnit : sig

  (** Some metadata about a given code unit. *)
  type t

  (** Return the name of the code unit that a symbol originated from. *)
  val origin : Global.t -> string

  (** The name of a given code unit *)
  val name : t -> string

  (** All of the code unit this unit directly imports *)
  val imports : t -> string list

  (** Create a code unit. *)
  val create : string -> t

  (** Add a binding to a given code unit. *)
  val add_global : Ident.t -> Domain.tp -> Domain.con option -> t -> (Global.t * t)

  (** Attempt to resolve an identifier a given code unit. *)
  val resolve_global : Ident.t -> t -> Global.t option

  (** Get the binding associated with a symbol. *)
  val get_global : Global.t -> t -> Domain.tp * Domain.con option

  (** Add another code unit as an import. *)
  val add_import : string list -> t -> t -> t
end
