type 'a t =
  | Nil
  | Node of Pos.t * Pos.t * 'a * 'a t * ('a t) * ('a t)

let empty = Nil

let rec lookup pos =
  function
  | Nil -> None
  | Node (lo, hi, u, cover, l, r) ->
    if (pos < lo) then
      lookup pos l
    else if (hi < pos) then
      lookup pos r
    else
      match lookup pos cover with
      | Some ui -> Some ui
      | None   -> Some u

let rec insert lo hi u =
  function
  | Nil -> Node (lo, hi, u, Nil, Nil, Nil)
  | Node (lo', hi', u', cover, l, r) ->
    if (hi < lo') then
      Node (lo', hi', u', cover, insert lo hi u l, r)
    else if (hi' < lo) then
      Node (lo', hi', u', cover, l, insert lo hi u r)
    else if (lo <= lo' && hi' <= hi) then
      Node (lo, hi, u, (Node (lo', hi', u', cover, Nil, Nil)), l, r)
    else
      Node (lo', hi', u', insert lo hi u cover, l, r)

let of_list xs = List.fold_left (fun t (lo, hi, u) -> insert lo hi u t) empty xs
