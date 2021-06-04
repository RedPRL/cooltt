open Basis

type t =
  | LvlVar of int
  | LvlMagic
  | LvlTop

(** Temporary measure until I finish adding this *)
val magic : t

val pp_lvl : t Pp.printer