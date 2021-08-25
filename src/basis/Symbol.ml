module J = Ezjsonm

module type S = sig
  type t

  val compare : t -> t -> int
  val equal : t -> t -> bool

  val pp : t Pp.printer
  val show : t -> string

  val serialize : t -> J.value
  val deserialize : J.value -> t
end
