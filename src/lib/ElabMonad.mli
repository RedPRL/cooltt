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
val push_var : CS.ident option -> D.tp -> 'a m -> 'a m
val add_global : CS.ident option -> D.tp -> D.t option -> Symbol.t m

val globally : 'a m -> 'a m

val resolve : CS.ident -> [`Local of int | `Global of Symbol.t | `Unbound] m
val get_global : Symbol.t -> D.nf m
val get_local_tp : int -> D.tp m
val get_local : int -> D.t m


val quote : D.tp -> D.t -> Syntax.t m
val quote_tp : D.tp -> Syntax.tp m
val quote_ne : D.ne -> Syntax.t m

val emit : (Format.formatter -> 'a -> unit) -> 'a -> unit m