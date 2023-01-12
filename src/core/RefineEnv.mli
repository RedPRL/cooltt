open Basis
open Bwd

open CodeUnit

module D := Domain

module Cell : sig
  type 'a t

  val contents : 'a t -> 'a
  val ident : 'a t -> Ident.t
end

type cell = (D.tp * D.con) Cell.t

type t
val init : t
val globally : t -> t

val locals : t -> (cell * bool) bwd
val size : t -> int
val get_local_tp : int -> t -> D.tp
val get_local : int -> t -> D.con
val resolve_local : Ident.t -> t -> int option

val set_fib : bool -> t -> t
val is_fib_only : t -> bool
val get_dom_bool : int -> t -> bool
val fib_only : t -> t

val local_cof_thy : t -> CofThy.Disj.t
val pp_env : t -> Pp.env
val sem_env : t -> D.env
val restrict : CofThy.cof list -> t -> t
val append_con : Ident.t -> D.con -> D.tp -> t -> t

val location : t -> LexingUtil.span option
val set_location : LexingUtil.span option -> t -> t

val dump : t Pp.printer
