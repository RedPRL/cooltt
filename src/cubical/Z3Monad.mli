module Theory :
sig
  type t
  val empty : t
  val assume : t -> CofThyData.cof -> t
  val test_sequent : t -> CofThyData.cof -> bool
  val consistency : t -> [`Consistent | `Inconsistent]
end
