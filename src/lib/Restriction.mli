type t
type dim = Domain.dim

exception Inconsistent

val emp : unit -> t


(* May raise Inconsistent *)
val equate : t -> dim -> dim -> t

val compare : t -> dim -> dim -> [`Same | `Apart | `Indet]
val equal : t -> dim -> dim -> bool

(** Checks whether a sequent is valid by left-inversion proof search *)
val test_sequent : t -> dim Cof.cof list -> dim Cof.cof -> bool