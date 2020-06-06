(* Due to Conchon & Filliatre *)

module type S =
sig
  type key
  type t

  val empty : t
  val test : key -> key -> t -> bool
  val union : key -> key -> t -> t
  val test_and_union : key -> key -> t -> bool * t
end

module type MAKER = functor (O : Map.OrderedType) -> S with type key = O.t

module Make : MAKER
