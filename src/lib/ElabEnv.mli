module CS := ConcreteSyntax
module D := Domain

open CoolBasis
open Bwd

module Cell : sig
  type t

  val tp : t -> D.tp
  val name : t -> string option
  val con : t -> D.con
end

type t
type cell = Cell.t

val locals : t -> cell bwd

val init : t
val append_el : string option -> D.con -> D.tp -> t -> t
val sem_env : t -> D.env
val pp_env : t -> Pp.env

val get_veil : t -> Veil.t
val veil : Veil.t -> t -> t

val size : t -> int

val resolve_local : CS.ident -> t -> int option
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.con