module type POSITION =
sig
  include Map.OrderedType
  val cut_span_after : t -> t * t -> t * t
  val cut_span_before : t -> t * t -> t * t
end

module type S = functor (Pos: POSITION) ->
sig
  type !+'a t
  val of_list : ((Pos.t * Pos.t) * 'a) list -> 'a t
  val lookup : Pos.t -> 'a t -> 'a option
end

module Make : S
