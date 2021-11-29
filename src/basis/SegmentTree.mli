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
  val of_list : ((Pos.t * Pos.t) * 'a) list -> 'a t
  val lookup : Pos.t -> 'a t -> 'a option
end

module Make : S
