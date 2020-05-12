module D := Domain

type env

(** Create an empty environment (uses a benign effect for now). *)
val init : unit -> env

(** Returns the consistency of the environment. *)
val consistency : env -> [`Consistent | `Inconsistent]

(** Assumes the truth of a cofibration; if it can be decomposed eagerly (conjunction of equations),
    then it does so immediately. Otherwise, it is held "on deck" and repeatedly decomposed when testing
    sequents. The function [consistency] will consider cofibrations on deck. *)
val assume : env -> D.cof -> env

(** Tests the validity of a sequent against the supplied environment. Equivalent to assuming
    the conjunction of the context and then testing truth. *)
val test_sequent : env -> D.cof list -> D.cof -> bool

(** Monadic interface *)
module M (M : CoolBasis.Monad.S) :
sig
  (** Search all branches induced by unreduced joins under additional cofibrations. *)
  val left_invert_under_cofs : env -> D.cof list -> (env -> unit M.m) -> unit M.m
end
