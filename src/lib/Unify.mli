module D := Domain
module EM := Monads.ElabM

val unify_tp : D.tp -> D.tp -> unit EM.m