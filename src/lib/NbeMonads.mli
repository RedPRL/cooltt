module D := Domain 
module S := Syntax
module St := ElabState

type 'a compute = St.t -> 'a
type 'a evaluate = St.t * D.env -> 'a
type 'a quote = St.t * int -> 'a

module CmpM : sig 
  include Monad.S with type 'a m = 'a compute
  val evaluate : D.env -> 'a evaluate -> 'a m
  val run : 'a m -> ElabState.t -> 'a
  val read : ElabState.t m
  val throw : exn -> 'a m
end

module EvM : sig 
  include Monad.S with type 'a m = 'a evaluate

  val compute : 'a compute -> 'a m

  val run : 'a m -> ElabState.t -> D.env -> 'a
  val read_global : ElabState.t m
  val read_local : D.env m
  val throw : exn -> 'a m

  val close_tp : S.tp -> (S.tp, D.tp) D.clo m
  val close2_tp : S.tp -> S.tp D.clo2 m
  val close3_tp : S.tp -> S.tp D.clo3 m
  val close_tm : S.t -> (S.t, D.t) D.clo m
  val close2_tm : S.t -> S.t D.clo2 m
  val push : D.t list -> 'a m -> 'a m
end

module QuM : sig 
  include Monad.S with type 'a m = 'a quote

  val compute : 'a compute -> 'a m

  val run : 'a m -> ElabState.t -> int -> 'a
  val read_global : ElabState.t m
  val read_local : int m
  val throw : exn -> 'a m

  val push : int -> 'a m -> 'a m
end