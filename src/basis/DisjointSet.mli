(* Due to Conchon & Filliatre *)

module type S =
sig
  type key
  type t

  val init : t
  val union : key -> key -> t -> t
  val find : key -> t -> key
end

module type MAKER = functor (O : Map.OrderedType) -> S with type key = O.t

module Make : MAKER
