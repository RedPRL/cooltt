module CS := ConcreteSyntax
module D := Domain
open CoolBasis.Bwd

type t
type cell = D.nf * string option

val locals : t -> cell bwd

val init : t
val append_el : string option -> D.con -> D.tp -> t -> t
val sem_env : t -> D.env
val get_veil : t -> Veil.t
val veil : Veil.t -> t -> t

val size : t -> int

val resolve_local : CS.ident -> t -> int option
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.con