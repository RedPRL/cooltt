module type S =
sig
  type key
  type t

  val init : t
  val union : key -> key -> t -> t
  val find : key -> t -> key
end

module type MAKER = functor (O : Map.OrderedType) -> S with type key = O.t

module Make : MAKER = functor (O : Map.OrderedType) ->
struct
  module T = PersistentTable.M (O)

  type key = O.t
  type t =
    {rank : int T.t;
     mutable parent : key T.t}

  let init =
    {rank = T.init;
     parent = T.init}


  let rec find_aux (x : key) (f : key T.t) =
    try
      let fx = T.get x f in
      if fx == x then
        f, x
      else
        let f, y = find_aux fx f in
        let f = T.set x y f in
        f, y
    with
    | _ ->
      let f = T.set x x f in
      f, x

  let find (x : key) (h : t) : key =
    let f, cx = find_aux x h.parent in
    h.parent <- f;
    cx

  let get_rank cx h =
    try
      T.get cx h.rank
    with
    | _ ->
      0

  let union (x : key) (y : key) (h : t) =
    let cx = find x h in
    let cy = find y h in
    if cx != cy then
      begin
        let rx = get_rank cx h in
        let ry = get_rank cy h in
        if rx > ry then
          {h with
           parent = T.set cy cx h.parent}
        else if rx < ry then
          {h with
           parent = T.set cx cy h.parent}
        else
          {rank = T.set cx (rx + 1) h.rank;
           parent = T.set cy cx h.parent}
      end
    else
      h
end
