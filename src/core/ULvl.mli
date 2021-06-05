open Basis

type t =
  | LvlVar of int
  | LvlGlobal of Symbol.t
  | LvlMagic
  | LvlTop

(** Temporary measure until I finish adding this *)
val magic : t

val equal : t -> t -> bool
val lt : t -> t -> bool
val leq : t -> t -> bool