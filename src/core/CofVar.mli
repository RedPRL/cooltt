open Basis

module Make : functor (Symbol : Symbol.S) -> sig
  type t =
    | Local of int
    | Axiom of Symbol.t

  val compare : t -> t -> int
  val dump : Format.formatter -> t -> unit
end
