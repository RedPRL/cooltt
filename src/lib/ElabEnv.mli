module CS := ConcreteSyntax
module D := Domain
open Bwd

type t
type cell = D.nf * string option

val locals : t -> cell bwd

val init : t
val push_term : string option -> D.t -> D.tp -> t -> t
val sem_env : t -> D.env

val size : t -> int

val resolve_local : CS.ident -> t -> int option
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.t