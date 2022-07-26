open Basis

module Make : functor (Symbol : Symbol.S) -> sig
  module CofVar := CofVar.Make(Symbol)
  type t =
    | DDim0
    (** The left endpoint of the abstract interval. *)

    | DDim1
    (** The right endpoint of the abstract interval. *)

    | DDimVar of CofVar.t
    (** In [cooltt], most dimension variables are represented as natural numbers (pointers into the context). *)

    | DDimProbe of DimProbe.t
    (** Some dimension variables must be generated to probe underneath a binder. Subject to substitution. *)

  val ddim0 : t
  val ddim1 : t
  val dvar : int -> t
  val daxiom : Symbol.t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val dump : t Pp.printer
end
