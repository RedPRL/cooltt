type t =
  | LvlVar of int
  | LvlMagic
  | LvlTop

(** Temporary measure until I finish adding this *)
val magic : t

val equal : t -> t -> bool
val lt : t -> t -> bool
val leq : t -> t -> bool