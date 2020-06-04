type alg_thy
type disj_thy
type cof = (Dim.dim, int) Cof.cof

(** Create an empty theory (uses a benign effect for now). *)
val init : unit -> disj_thy

(** Returns the consistency of the theory. *)
val consistency : disj_thy -> [`Consistent | `Inconsistent]

(** Assumes the truth of a cofibration; if it can be decomposed eagerly (conjunction of equations),
    then it does so immediately. Otherwise, it is held "on deck" and repeatedly decomposed when testing
    sequents. The function [consistency] will consider cofibrations on deck. *)
val assume : disj_thy -> cof -> disj_thy
val assumes : disj_thy -> cof list -> disj_thy

(** Tests the validity of a sequent against the supplied theory. Equivalent to assuming
    the conjunction of the context and then testing truth. *)
val test_sequent : disj_thy -> cof list -> cof -> bool

(** Search all branches induced by irreducible joins under additional cofibrations. *)
val left_invert_under_cofs
  : zero:'a
  (** [zero] is the default value for vacuous cases. *)
  -> seq:((cof -> 'a) -> cof list -> 'a)
  (** [seq] is the sequencing operator. *)
  -> disj_thy
  -> cof list
  -> (disj_thy -> 'a)
  -> 'a

module Algebraic :
sig
  val init : unit -> alg_thy

  (** Construct the enveloping disjunctive theory of an algebraic theory. *)
  val disj_envelope : alg_thy -> disj_thy

  (** Partition a disjunctive theory into algebraic parts and disjunctive parts. *)
  val partition_thy : disj_thy -> alg_thy * cof list

  (** Assemble algebraic parts and disjunctive parts. *)
  val assemble_thy : alg_thy -> cof list -> disj_thy

  (** Returns the consistency of the theory. *)
  val consistency : alg_thy -> [`Consistent | `Inconsistent]

  (** Search all branches induced by irreducible joins under additional cofibrations. *)
  val left_invert_under_cofs
    : zero:'a
    (** [zero] is the default value for vacuous cases. *)
    -> seq:((cof -> 'a) -> cof list -> 'a)
    (** [seq] is the sequencing operator. *)
    -> alg_thy
    -> cof list
    -> (alg_thy -> 'a)
    -> 'a
end
