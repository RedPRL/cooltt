open Core
open CodeUnit

val init : string -> int -> unit
val close : unit -> unit

val dispatch_goal : (Ident.t * Syntax.tp) list -> Syntax.tp -> unit
