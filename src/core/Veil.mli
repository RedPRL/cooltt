open Basis

module Global = CodeUnit.Global

(* Translucent: visible to conversion, invisible to quote
   Transparent: visible to conversion, visible to quote *)
type policy = [`Translucent | `Transparent]

type t

val const : policy -> t
val unfold : Global.t list -> t -> t

val policy : Global.t -> t -> policy

val pp : t Pp.printer
val show : t -> string
