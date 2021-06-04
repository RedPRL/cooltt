type t =
  | LvlVar of int
  | LvlMagic
  | LvlSuc of t

let magic = LvlMagic