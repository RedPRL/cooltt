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

module Make : S = functor (Pos : POSITION) ->
struct

  module Span = struct
    type t = Pos.t * Pos.t
    let compare = CCPair.compare Pos.compare (CCOrd.opp Pos.compare)
  end

  module SegTree = CCMap.Make(Span)

  type !+'a t = 'a SegTree.t

  let lookup pos t =
    match SegTree.find_last_opt (fun k -> Span.compare k (pos,pos) <= 0) t with
    | None -> None
    | Some ((_, stop), v) ->
      if Pos.compare stop pos >= 0 then Some v else None

  let of_sorted_list l =
    let rec loop tree stack l =
      match l, stack with
      | _, [] -> SegTree.add_list tree stack
      | [], x :: l -> loop tree [x] l
      | (((xstart, xstop) as xk, xv) as x) :: stack, (((ystart, ystop), _) as y :: l) ->
        if Pos.compare ystop xstart < 0 then
          loop tree (y :: x :: stack) l
        else if Pos.compare xstop ystart < 0 then
          loop (SegTree.add xk xv tree) stack (y :: l)
        else
          (let tree =
             if Pos.compare xstart ystart < 0 then
               SegTree.add (Pos.cut_span_after ystart xk) xv tree
             else
               tree
           in
           if Pos.compare xstop ystop > 0 then
             loop tree (y :: (Pos.cut_span_before ystop xk, xv) :: stack) l
           else
             loop tree stack (y :: l))
    in
    loop SegTree.empty [] l

  let of_list l =
    of_sorted_list (CCList.sort (CCOrd.(>|=) Span.compare fst) l)
end
