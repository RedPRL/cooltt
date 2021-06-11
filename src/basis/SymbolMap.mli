
module type S =
sig
  include Map.S

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module Make (Sym : Symbol.S) : S with type key = Sym.t
