module D := Domain
module S := Syntax
open Monads

val quote_con : D.tp -> D.con -> S.t quote
val quote_tp : D.tp -> S.tp quote
val quote_cut : D.tp -> D.cut -> S.t quote
val quote_cof : D.cof -> S.t quote
