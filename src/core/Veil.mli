open Basis

(* Translucent: visible to conversion, invisible to quote
   Transparent: visible to conversion, visible to quote *)
type t = [`Translucent | `Transparent]

val pp : t Pp.printer
val show : t -> string
