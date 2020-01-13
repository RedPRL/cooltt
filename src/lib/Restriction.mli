type t
type dim = Domain.dim

exception Inconsistent

val emp : unit -> t

(* May raise Inconsistent *)
val equate : dim -> dim -> t -> t
val compare : dim -> dim -> t -> [`Same | `Apart | `Indet]