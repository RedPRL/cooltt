
(* Translucent: visible to conversion, invisible to quote
   Transparent: visible to conversion, visible to quote *)
type policy = [`Translucent | `Transparent]

type t 

val const : policy -> t
val policy : Symbol.t -> t -> policy