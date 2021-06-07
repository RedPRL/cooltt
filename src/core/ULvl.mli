open Basis

type shift

val const_shift : int -> shift

type t =
  | LvlShiftedVar of {var: int; shift: shift}
  | LvlShiftedGlobal of {sym: Symbol.t; shift: shift}
  | LvlMagic
  | LvlTop

(** Temporary measure until I finish adding this *)
val magic : t

val var : int -> t
val global : Symbol.t -> t
val equal : t -> t -> bool
val lt : t -> t -> bool
val leq : t -> t -> bool

val apply : shift -> t -> t
val pp_shift : shift Pp.printer
