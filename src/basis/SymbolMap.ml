module type S =
sig
  include Map.S

  val pp : (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module Make (S : Symbol.S) =
struct
  include Map.Make (S)

  let pp _ih fmt _table =
    Format.fprintf fmt "<globals>"
end
