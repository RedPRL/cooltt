type policy = [`Opaque | `Translucent | `Transparent]

type t 
val default : t
val policy : Symbol.t -> t -> policy