type t =
  | LvlVar of int
  | LvlMagic
  | LvlTop

let magic = LvlMagic

let equal x y =
  x = y || x = LvlMagic || y = LvlMagic

let lt x y =
  match x, y with
  | LvlMagic, _ -> true
  | _, LvlMagic -> true
  | LvlVar _, LvlTop -> true
  | _ -> false

let leq x y =
  equal x y || lt x y