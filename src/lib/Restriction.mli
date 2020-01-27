type t
type dim = Domain.dim

val emp : unit -> t

val status : t -> [`Consistent | `Inconsistent]


val equate : t -> dim -> dim -> t

(** Checks whether a sequent is valid by left-inversion proof search *)
val test_sequent : t -> dim Cof.cof list -> dim Cof.cof -> bool