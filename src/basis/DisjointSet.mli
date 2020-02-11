(* Due to Conchon & Filliatre *)

module type S =
sig
  type 'a t

  val init : size:int -> 'a t
  val union : 'a -> 'a -> 'a t -> 'a t
  val find : 'a -> 'a t -> 'a
end

module Make (T : PersistentTable.S) : S
