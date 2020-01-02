module CS := ConcreteSyntax
module S := Syntax
module EM := ElabMonad
module D := Domain

val check_tp : CS.t -> S.tp EM.m
val check_tm : CS.t -> D.tp -> S.t EM.m

val eval_tp : S.tp -> D.tp EM.m
val eval_tm : S.t -> D.t EM.m