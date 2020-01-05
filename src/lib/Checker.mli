module CS := ConcreteSyntax
module S := Syntax
module EM := Monads.ElabM
module D := Domain

open Refiner

val chk_tp : S.tp -> tp_tac
val chk_tm : S.t -> chk_tac
val syn_tm : S.t -> syn_tac