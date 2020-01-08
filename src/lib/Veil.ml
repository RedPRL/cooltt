type policy = [`Translucent | `Transparent]
type t = Symbol.t -> policy

let policy : Symbol.t -> t -> policy =
  fun sym veil -> veil sym

let const : policy -> t = 
  fun pol _ ->
  pol