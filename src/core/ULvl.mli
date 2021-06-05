open Basis

(** [[10;20;22;23;24;...]] is represented as [{init=10;steps=[10;2]}] because
    the first element is [10] and the steps between adjacent elementns are [[10;2;1;1;...]].
    The infinite suffix [[1;1;...]] should not be part of the encoding. *)
type shift =
  { init: int
  ; steps: int list (** invariants: all numbers > 0 and the last element > 1 *)
  }

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
