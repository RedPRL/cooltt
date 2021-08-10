open Core
open CodeUnit

type t

val init : int -> t
val close : t -> unit

val dispatch_goal : t -> (Ident.t * Syntax.tp) list -> Syntax.tp -> unit
