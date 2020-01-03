module Env := ElabEnv
module CS := ConcreteSyntax
module D := Domain

include Monad.S

type 'a result = 
  | Ret of 'a
  | Throw of exn

val read : Env.t m
val throw : exn -> 'a m
val run : 'a m -> Env.t -> 'a result 
val push_var : CS.ident -> D.tp -> 'a m -> 'a m