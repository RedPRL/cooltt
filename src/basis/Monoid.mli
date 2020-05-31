module type S = sig
  type key
  type t
  val zero : t
  val seq : (key -> t) -> key list -> t
end
