type t =
  | LvlVar of int
  | LvlMagic
  | LvlTop

let magic = LvlMagic