module type POSITION =
sig
  include Map.OrderedType
  type range = { start : t; stop: t }
  val cut_range_after : t -> range -> range
  val cut_range_before : t -> range -> range
end

module type S = functor (Pos: POSITION) ->
sig
  type !+'a t
  val lookup : Pos.t -> 'a t -> 'a option
  val containing : Pos.t -> 'a t -> 'a list
  val of_list : (Pos.range * 'a) list -> 'a t
  val empty : 'a t

  val pp : (Format.formatter -> Pos.range -> unit) -> (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a t -> unit
end

module Make : S
