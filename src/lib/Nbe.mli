module D := Domain
module S := Syntax
module St := ElabState

open CoolBasis

exception NbeFailed of string

open Monads
val eval : S.t -> D.con evaluate
val eval_tp : S.tp -> D.tp evaluate
val quote : D.tp -> D.con -> S.t quote
val quote_tp : D.tp -> S.tp quote
val quote_ne : D.ne -> S.t quote
val equal : D.tp -> D.con -> D.con -> bool quote
val equal_tp : D.tp -> D.tp -> bool quote
val equal_ne : D.ne -> D.ne -> bool quote

val inst_tp_clo : 'n D.tp_clo -> ('n, D.con) Vec.vec -> D.tp compute
val inst_tm_clo : 'n D.tm_clo -> ('n, D.con) Vec.vec -> D.con compute