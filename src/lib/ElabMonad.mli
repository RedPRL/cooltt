module Env := ElabEnv
module St := ElabState
module CS := ConcreteSyntax
module D := Domain

include Monad.S

type 'a result = 
  | Ret of 'a
  | Throw of exn

val read : Env.t m
val get : St.t m
val set : St.t -> unit m

val lift_qu : 'a NbeMonads.quote -> 'a m
val lift_ev : 'a NbeMonads.evaluate -> 'a m
val lift_cmp : 'a NbeMonads.compute -> 'a m

val throw : exn -> 'a m
val run : 'a m -> Env.t -> 'a result 
val local : (Env.t -> Env.t) -> 'a m -> 'a m
val globally : 'a m -> 'a m
val emit : (Format.formatter -> 'a -> unit) -> 'a -> unit m