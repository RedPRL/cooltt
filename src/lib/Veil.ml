type policy = [`Translucent | `Transparent]
type t = Symbol.t -> policy

let policy : Symbol.t -> t -> policy =
  fun sym veil -> veil sym

let unfold _sym _veil _sym' = 
  `Transparent
(* if sym = sym' then `Transparent else veil sym' *)

let const : policy -> t = 
  fun pol _ ->
  pol