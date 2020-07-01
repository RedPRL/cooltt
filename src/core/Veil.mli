open Basis

(* Translucent: visible to conversion, invisible to quote
   Transparent: visible to conversion, visible to quote *)
type policy = [`Translucent | `Transparent]

type t

val const : policy -> t
val unfold : Symbol.t list -> t -> t

val policy : Symbol.t -> t -> policy

val pp : t Pp.printer
val show : t -> string
