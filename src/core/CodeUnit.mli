open Basis

module J = Ezjsonm

module CodeUnitID :
sig
  type t
  val compare : t -> t -> int
  val pp : t Pp.printer
  val top_level : t
  val file : string -> t
end
type id = CodeUnitID.t

module Global :
sig
  include Symbol.S
end

module Domain : module type of Domain.Make(Global)
module Syntax : module type of Syntax.Make(Global)
module CofVar : module type of CofVar.Make(Global)
module CofBuilder : module type of CofBuilder.Make(Global)
module CofThy : module type of CofThy.Make(Global)

module CodeUnit : sig

  (** Some metadata about a given code unit. *)
  type t

  (** Return the name of the code unit that a symbol originated from. *)
  val origin : Global.t -> id

  (** The name of a given code unit *)
  val id : t -> id

  (** Create a code unit. *)
  val create : id -> t

  (** Add a binding to a given code unit. *)
  val add_global : Ident.t -> Domain.tp -> Domain.con option -> t -> (Global.t * t)

  (** Get the binding associated with a symbol. *)
  val get_global : Global.t -> t -> Domain.tp * Domain.con option
end
