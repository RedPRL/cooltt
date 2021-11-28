type 'a t =
  | Nil
  | Node of Pos.range * 'a * 'a t * 'a t * 'a t

let empty = Nil

let rec lookup pos =
  function
  | Nil -> None
  | Node (range, u, l, inner, r) ->
    if (pos < range.start) then
      lookup pos l
    else if (range.stop < pos) then
      lookup pos r
    else
      match lookup pos inner with
      | Some ui -> Some ui
      | None   -> Some u

let rec containing (range : Pos.range) =
  function
  | Nil -> []
  | Node (range', u, l, inner, r) ->
    if (range.stop < range'.start) then
      containing range l
    else if (range'.stop < range.start) then
      containing range r
    else if (range.start <= range'.start && range'.stop <= range.stop) then
      []
    else
      u :: containing range inner

let rec insert (range : Pos.range) u =
  function
  | Nil -> Node (range, u, Nil, Nil, Nil)
  | Node (range', u', l, inner, r) ->
    if (range.stop < range'.start) then
      Node (range', u', insert range u l, inner, r)
    else if (range'.stop < range.start) then
      Node (range', u', l, inner, insert range u r)
    else if (range.start <= range'.start && range'.stop <= range.stop) then
      (* The span we are inserting contains range', so we make a new node, and add range' to the interior. *)
      Node (range, u, l, (Node (range', u', Nil, inner, Nil)), r)
    else
      (* range' contains the span we are trying to insert, so we insert it into the interior. *)
      Node (range', u', l, insert range u inner, r)

let of_list xs = List.fold_left (fun t (range, u) -> insert range u t) empty xs
