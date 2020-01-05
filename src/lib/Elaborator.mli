module CS := ConcreteSyntax
module S := Syntax
module EM := Monads.ElabM
module D := Domain

open Refiner

val chk_tp : CS.t -> tp_tac
val chk_tm : CS.t -> chk_tac 
val syn_tm : CS.t -> syn_tac