module Theory :
sig
  type t
  val test_sequent : t -> CofThyData.cof -> bool
  val consistency : t -> [`Consistent | `Inconsistent]
  val assume : t -> CofThyData.cof -> t
end
