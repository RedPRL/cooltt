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
  val of_list : (Pos.range * 'a) list -> 'a t
  val lookup : Pos.t -> 'a t -> 'a option
end

module Make : S = functor (Pos : POSITION) ->
struct

  module Range = struct
    type t = Pos.range
    let compare (x : t) (y : t) =
      CCOrd.(Pos.compare x.start y.start <?> (opp Pos.compare, x.stop, y.stop))
  end

  module SegTree = CCMap.Make(Range)

  type !+'a t = 'a SegTree.t

  let lookup pos t =
    match SegTree.find_last_opt (fun k -> Range.compare k {start = pos; stop = pos} <= 0) t with
    | None -> None
    | Some (r, v) ->
      if Pos.compare r.stop pos >= 0 then Some v else None

  let of_sorted_list l =
    let rec loop tree stack l =
      match stack, l with
      | _, [] -> SegTree.add_list tree stack
      | [], x :: l -> loop tree [x] l
      | ((xk, xv) as x) :: stack, ((yk, _) as y :: l) ->
        if Pos.compare yk.stop xk.start < 0 then
          loop tree (y :: x :: stack) l
        else if Pos.compare xk.stop yk.start < 0 then
          loop (SegTree.add xk xv tree) stack (y :: l)
        else
          let tree =
            if Pos.compare xk.start yk.start < 0 then
              SegTree.add (Pos.cut_range_after yk.start xk) xv tree
            else
              tree
          in
          if Pos.compare xk.stop yk.stop > 0 then
            loop tree (y :: (Pos.cut_range_before yk.stop xk, xv) :: stack) l
          else
            loop tree stack (y :: l)
    in
    loop SegTree.empty [] l

  let of_list l =
    of_sorted_list (CCList.sort (CCOrd.(>|=) Range.compare fst) l)
end
