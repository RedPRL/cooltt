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
val throw : exn -> 'a m
val run : 'a m -> Env.t -> 'a result 
val push_var : CS.ident -> D.tp -> 'a m -> 'a m
val add_global : CS.ident -> D.tp -> D.t -> unit m

val resolve : CS.ident -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> D.nf m
val get_local : int -> D.tp m


val quote : D.nf -> Syntax.t m

val emit : (Format.formatter -> 'a -> unit) -> 'a -> unit m