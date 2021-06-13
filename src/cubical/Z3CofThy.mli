type t
val empty : t
val assume : t -> CofThyData.cof list -> t
val test_sequent : t -> CofThyData.cof -> bool
val consistency : t -> [`Consistent | `Inconsistent]
val assume_vars : t -> CofThyData.var list -> t
