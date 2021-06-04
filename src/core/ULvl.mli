type t =
  | LvlVar of int
  | LvlMagic

(** Temporary measure until I finish adding this *)
val magic : t