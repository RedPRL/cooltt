type reduced_env
type env
type cof = (Dim.dim, int) Cof.cof

(** Create an empty environment (uses a benign effect for now). *)
val init : unit -> env

(** Returns the consistency of the environment. *)
val consistency : env -> [`Consistent | `Inconsistent]

(** Assumes the truth of a cofibration; if it can be decomposed eagerly (conjunction of equations),
    then it does so immediately. Otherwise, it is held "on deck" and repeatedly decomposed when testing
    sequents. The function [consistency] will consider cofibrations on deck. *)
val assume : env -> cof -> env

(** Tests the validity of a sequent against the supplied environment. Equivalent to assuming
    the conjunction of the context and then testing truth. *)
val test_sequent : env -> cof list -> cof -> bool

(** Search all branches induced by unreduced joins under additional cofibrations. *)
val left_invert_under_cofs : zero:'a  
  (** [zero] is the default value for vacuous cases. *)
  -> seq:((cof -> 'a) -> cof list -> 'a)
  (** [seq] is the sequencing operator. *)
  -> env -> cof list -> (env -> 'a) -> 'a

module Reduced :
sig
  (** Create an environment with no unreduced joins. *)
  val to_env : reduced_env -> env

  (** Partition an env into reduced parts and unreduced parts. *)
  val partition_env : env -> reduced_env * cof list

  (** Assemble reduced parts and unreduced parts. *)
  val assemble_env : reduced_env -> cof list -> env

  (** Returns the consistency of the environment. *)
  val consistency : reduced_env -> [`Consistent | `Inconsistent]

  (** Search all branches induced by unreduced joins under additional cofibrations. *)
  val left_invert_under_cofs : zero:'a  
    (** [zero] is the default value for vacuous cases. *)
    -> seq:((cof -> 'a) -> cof list -> 'a)
    (** [seq] is the sequencing operator. *)
    -> reduced_env -> cof list -> (reduced_env -> 'a) -> 'a
end
