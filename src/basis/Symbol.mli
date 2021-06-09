(* FIXME: This is anti-modular, but it makes the symbol
   table code less janky for now.
 *)
type t = { origin : string; index : int; name : string option}

val compare : t -> t -> int
val equal : t -> t -> bool

(* These two functions still inspire (???). Perhaps we ought to use a different
   Construct for these fresh dimension variables.
 *)

(** Create a fresh symbol for probing cofibrations. *)
val fresh_probe : unit -> t

(** Create a fresh symbol for performing coercions *)
val fresh_coe : unit -> t

val pp : t Pp.printer
val show : t -> string
