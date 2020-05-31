module type S = sig
  type t
  val zero : t
  val seq : ('a -> t) -> 'a list -> t
end
