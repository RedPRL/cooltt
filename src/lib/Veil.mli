
(* Translucent: visible to conversion, invisible to quote
   Transparent: visible to conversion, visible to quote *)
type policy = [`Translucent | `Transparent]

type t 
val default : t
val policy : Symbol.t -> t -> policy