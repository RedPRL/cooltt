module D := Domain
module S := Syntax
open Monads

val quote_con : D.tp -> D.con -> S.t quote 
val quote_tp : D.tp -> S.tp quote
val quote_cut : D.cut -> S.t quote
val quote_cof : D.cof -> S.t quote
val quote_dim : D.dim -> S.t quote

val con_splitter : S.tp -> (D.cof * S.t quote) list -> S.t quote
val tp_splitter : (D.cof * S.tp quote) list -> S.tp quote
val cof_splitter : (D.cof * S.t quote) list -> S.t quote
