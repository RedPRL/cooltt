module type S =
sig
  type 'a t

  val init : size:int -> 'a t
  val union : 'a -> 'a -> 'a t -> 'a t
  val find : 'a -> 'a t -> 'a
end

module Make (T : PersistentTable.S) : S =
struct
  type 'a t =
    {rank : ('a, int) T.t;
     mutable parent : ('a, 'a) T.t}

  let init ~size =
    {rank = T.init ~size;
     parent = T.init ~size}


  let rec find_aux (x : 'a) (f : ('a, 'a) T.t) =
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

  let find (x : 'a) (h : 'a t) : 'a =
    let f, cx = find_aux x h.parent in
    h.parent <- f;
    cx

  let get_rank cx h =
    try
      T.get cx h.rank
    with
    | _ ->
      0

  let union (x : 'a) (y : 'a) (h : 'a t) =
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
