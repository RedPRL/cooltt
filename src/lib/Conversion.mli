module D := Domain
module S := Syntax
module St := ElabState
module Splice := Splice

exception NbeFailed of string

open Monads

val equal_con : D.tp -> D.con -> D.con -> bool quote
val equal_tp : D.tp -> D.tp -> bool quote

val equate_con : D.tp -> D.con -> D.con -> unit quote
val equate_tp : D.tp -> D.tp -> unit quote