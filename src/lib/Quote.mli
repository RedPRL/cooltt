module D := Domain
module S := Syntax
open Monads

val quote'_con : D.tp -> D.con -> S.t quote'
val quote'_tp : D.tp -> S.tp quote'
val quote'_cut : D.tp -> D.cut -> S.t quote'
val quote'_cof : D.cof -> S.t quote'
val quote'_dim : D.dim -> S.t quote'
