module D := Domain

type env

(** Create an empty environment (uses a benign effect for now). *)
val init : unit -> env

(** Creates the inconsistent environment. *)
val inconsistent : env

(** Returns whether the environment is inconsistent. This is guaranteed to return the correct answer,
    even though it may not literally check 0=1. *)
val status : env -> [`Consistent of D.cof | `Inconsistent]

val unreduced_assumptions : env -> D.cof

(** Assumes the truth of a cofibration; if it can be decomposed eagerly (conjunction of equations),
    then it does so immediately. Otherwise, it is held "on deck" and repeatedly decomposed when testing
    sequents. *)
val assume : env -> D.cof -> env

(** Equivalent to [assume env (Cof.eq r s)] *)
val equate : env -> D.dim -> D.dim -> env

(** Tests the truth of a cofibration against the supplied environment. *)
val test : env -> D.cof -> bool

(** Tests the validity of a sequent against the supplied environment. Equivalent to assuming
    the conjunction of the context and then testing truth. *)
val test_sequent : env -> D.cof list -> D.cof -> bool
