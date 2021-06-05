open Basis

type t =
  | LvlVar of int
  | LvlGlobal of Symbol.t
  | LvlMagic
  | LvlTop

let magic = LvlMagic

let equal x y =
  match x, y with
  | LvlGlobal x, LvlGlobal y -> Symbol.equal x y
  | _ -> x = y || x = LvlMagic || y = LvlMagic

let lt x y =
  match x, y with
  | LvlMagic, _ -> true
  | _, LvlMagic -> true
  | (LvlVar _ | LvlGlobal _), LvlTop -> true
  | _ -> false

let leq x y =
  equal x y || lt x y