module CS := ConcreteSyntax
module D := Domain

open CoolBasis
open Bwd

module ConCell : sig
  type t

  val tp : t -> D.tp
  val visibility : t -> [`Visible | `Hidden]
  val name : t -> string option
  val con : t -> D.con
end

type t
type cell = [`Con of ConCell.t]

val locals : t -> cell bwd

val init : t
val append_con : string option -> D.con -> D.tp -> t -> t
val sem_env : t -> D.env
val pp_env : t -> Pp.env
val restriction : t -> Restriction.t

val get_veil : t -> Veil.t
val set_veil : Veil.t -> t -> t

val size : t -> int

val resolve_local : CS.ident -> t -> int option
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.con

val problem : t -> string bwd
val push_problem : string -> t -> t