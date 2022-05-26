open Basis

module Make : functor (Symbol : Symbol.S) -> sig
  module CofVar := CofVar.Make(Symbol)
  type t =
    | Dim0
    (** The left endpoint of the abstract interval. *)

    | Dim1
    (** The right endpoint of the abstract interval. *)

    | DimVar of CofVar.t
    (** In [cooltt], most dimension variables are represented as natural numbers (pointers into the context). *)

    | DimProbe of DimProbe.t
    (** Some dimension variables must be generated to probe underneath a binder. Subject to substitution. *)

  val dim0 : t
  val dim1 : t
  val var : int -> t
  val axiom : Symbol.t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int

  val dump : t Pp.printer
end
