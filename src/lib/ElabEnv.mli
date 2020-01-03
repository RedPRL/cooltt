module CS := ConcreteSyntax
module D := Domain

type t
type cell = D.nf * string option

val locals : t -> cell list

val init : t
val push_term : string option -> D.t -> D.tp -> t -> t
val to_sem_env : t -> D.env

val size : t -> int

val resolve_local : CS.ident -> t -> int option
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.t