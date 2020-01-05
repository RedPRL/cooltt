module Env := ElabEnv
module St := ElabState
module CS := ConcreteSyntax
module D := Domain

include Monad.MonadReaderStateResult 
  with type global := St.t
  with type local := Env.t

val lift_qu : 'a NbeMonads.quote -> 'a m
val lift_ev : 'a NbeMonads.evaluate -> 'a m
val lift_cmp : 'a NbeMonads.compute -> 'a m

val globally : 'a m -> 'a m
val emit : (Format.formatter -> 'a -> unit) -> 'a -> unit m