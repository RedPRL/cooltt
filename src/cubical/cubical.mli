(** The {!module:Cubical} library implements the syntax and semantics of the Cartesian interval as well as a logic of cofibrations as described by {{:https://github.com/dlicata335/cart-cube/blob/master/cart-cube.pdf} ABCFHL}. *)

(** {1 Syntax} *)

(** The abstract syntax of the Cartesian interval. *)
module Dim : module type of Dim

(** The abstract syntax of the restricted predicate logic of cofibrations. *)
module Cof : module type of Cof

module DimProbe : module type of DimProbe

(** {1 Semantics} *)

open Basis

(** The {!module:CofThy} module implements decision procedures for sequents relative to a theory over the interval, stated in the language of cofibrations. *)
module CofThy :
sig
  type cof = (Dim.dim, [`L of int | `G of Symbol.t]) Cof.cof

  (** Algebraic theories over the interval. *)
  module Alg :
  sig
    (** The type of an algebraic theory (no unreduced joins). *)
    type t

    (** The empty theory. *)
    val empty : t

    (** Returns the consistency of the theory. *)
    val consistency : t -> [`Consistent | `Inconsistent]

    (** Search all branches induced by irreducible joins under additional cofibrations. *)
    val left_invert_under_cofs
      : zero:'a
      (** [zero] is the default value for vacuous cases. *)
      -> seq:((t -> 'a) -> t list -> 'a)
      (** [seq] is the sequencing operator. *)
      -> t
      (** the theory *)
      -> cof list
      (** the cofibration context *)
      -> (t -> 'a)
      (** the continuation *)
      -> 'a
  end

  (** Disjunctive theories over the interval. *)
  module Disj :
  sig
    (** The type of a disjunctive theory. *)
    type t

    (** The empty theory. *)
    val empty : t

    (** Construct the enveloping disjunctive theory of an algebraic theory. *)
    val envelope_alg : Alg.t -> t

    (** Returns the consistency of the theory. *)
    val consistency : t -> [`Consistent | `Inconsistent]

    (** Assumes the truth of a cofibration. *)
    val assume : t -> cof list -> t

    (** Tests the validity of a sequent against the supplied theory. Equivalent to assuming
        the conjunction of the context and then testing truth. *)
    val test_sequent : t -> cof list -> cof -> bool

    (** Search all branches induced by irreducible joins under additional cofibrations. *)
    val left_invert
      : zero:'a
      (** [zero] is the default value for vacuous cases. *)
      -> seq:((Alg.t -> 'a) -> Alg.t list -> 'a)
      (** [seq] is the sequencing operator. *)
      -> t
      (** the theory *)
      -> (Alg.t -> 'a)
      (** the continuation *)
      -> 'a
  end
end
