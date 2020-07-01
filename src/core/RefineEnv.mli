module D := Domain

open Basis
open Cubical
open Bwd

module Cell : sig
  type 'a t

  val contents : 'a t -> 'a
  val ident : 'a t -> Ident.t
end

type cell = (D.tp * D.con) Cell.t

type t
val init : t

val size : t -> int
val locals : t -> cell bwd
val sem_env : t -> D.env
val pp_env : t -> Pp.env
val cof_thy : t -> CofThy.Disj.t
val get_veil : t -> Veil.t

val location : t -> LexingUtil.span option
val set_location : LexingUtil.span option -> t -> t

val append_con : Ident.t -> D.con -> D.tp -> t -> t

val set_veil : Veil.t -> t -> t

val resolve_local : Ident.t -> t -> int option
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.con
