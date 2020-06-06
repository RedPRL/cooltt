type cof = (Dim.dim, int) Cof.cof
type alg_thy
type disj_thy

module Alg :
sig
  (** The type of an algebraic theory (no unreduced joins). *)
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
    (** the theory *)
    -> cof list
    (** the cofibration context *)
    -> (t -> 'a)
    (** the continuation *)
    -> 'a
end

module Disj :
sig
  (** The type of a disjunctive theory. *)
  type t = disj_thy

  (** The empty theory. *)
  val init : t

  (** Returns the consistency of the theory. *)
  val consistency : t -> [`Consistent | `Inconsistent]

  (** Assumes the truth of a cofibration. *)
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
    (** the theory *)
    -> (alg_thy -> 'a)
    (** the continuation *)
    -> 'a
end
