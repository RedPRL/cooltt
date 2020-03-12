module D := Domain 
module S := Syntax
module St := ElabState
open CoolBasis

type 'a compute 
type 'a evaluate
type 'a quote

module CmpM : sig 
  include Monad.MonadReaderResult 
    with type 'a m = 'a compute

  val lift_ev : D.env -> 'a evaluate -> 'a m
  val test_sequent : D.cof list -> D.cof -> bool m
end

module EvM : sig 
  include Monad.MonadReaderResult 
    with type 'a m = 'a evaluate

  val lift_cmp : 'a compute -> 'a m

  val read_global : ElabState.t m
  val read_local : D.env m

  val close_tp : S.tp -> 'n D.tp_clo m
  val close_tm : S.t -> 'n D.tm_clo m
  val append : D.con list -> 'a m -> 'a m
end

module QuM : sig 
  include Monad.MonadReaderResult 
    with type 'a m = 'a quote

  val lift_cmp : 'a compute -> 'a m

  val read_global : ElabState.t m
  val read_local : int m
  val read_veil : Veil.t m

  val binder : int -> 'a m -> 'a m
  val bind_cof_proof : D.cof -> 'a m -> [`Ret of 'a | `Abort] m

  (* like bind_cof_proof, but doesn't increase the de bruijn index *)
  val restrict : D.cof -> 'a m -> [`Ret of 'a | `Abort] m

  val abort_if_inconsistent : 'a -> 'a m -> 'a m
end

module ElabM : sig
  include Monad.MonadReaderStateResult 
    with type global := St.t
    with type local := ElabEnv.t

  val lift_qu : 'a quote -> 'a m
  val lift_ev : 'a evaluate -> 'a m
  val lift_cmp : 'a compute -> 'a m

  val veil : Veil.t -> 'a m -> 'a m

  val globally : 'a m -> 'a m
  val emit : (Format.formatter -> 'a -> unit) -> 'a -> unit m
end