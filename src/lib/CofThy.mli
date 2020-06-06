type cof = (Dim.dim, int) Cof.cof
type alg_thy
type disj_thy

module Alg :
sig
  type t = alg_thy

  (** Create an empty theory. *)
  val init : t

  (** Returns the consistency of the theory. *)
  val consistency : t -> [`Consistent | `Inconsistent]

  (** Construct the enveloping disjunctive theory of an algebraic theory. *)
  val disj_envelope : alg_thy -> disj_thy

  (** Search all branches induced by irreducible joins under additional cofibrations. *)
  val left_invert_under_cofs
    : zero:'a
    (** [zero] is the default value for vacuous cases. *)
    -> seq:((t -> 'a) -> t list -> 'a)
    (** [seq] is the sequencing operator. *)
    -> t
    -> cof list
    -> (t -> 'a)
    -> 'a
end

module Disj :
sig
  type t = disj_thy

  (** Create an empty theory (uses a benign effect for now). *)
  val init : t

  (** Returns the consistency of the theory. *)
  val consistency : t -> [`Consistent | `Inconsistent]

  (** Assumes the truth of a cofibration; if it can be decomposed eagerly (conjunction of equations),
      then it does so immediately. Otherwise, it is held "on deck" and repeatedly decomposed when testing
      sequents. The function [consistency] will consider cofibrations on deck. *)
  val assume : t -> cof list -> disj_thy

  (** Tests the validity of a sequent against the supplied theory. Equivalent to assuming
      the conjunction of the context and then testing truth. *)
  val test_sequent : t -> cof list -> cof -> bool

  (** Search all branches induced by irreducible joins under additional cofibrations. *)
  val left_invert
    : zero:'a
    (** [zero] is the default value for vacuous cases. *)
    -> seq:((alg_thy -> 'a) -> alg_thy list -> 'a)
    (** [seq] is the sequencing operator. *)
    -> t
    -> (alg_thy -> 'a)
    -> 'a
end

(*
module Algebraic :
sig
  (** Assemble algebraic parts and disjunctive parts. *)
  val assemble_thy : alg_thy -> cof list -> disj_thy
end
*)
