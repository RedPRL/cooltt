module CS := ConcreteSyntax
module S := Syntax
module EM := Monads.ElabM
module D := Domain

open Refiner

val check_tp : S.tp -> tp_tac
val check_tm : S.t -> chk_tac
val synth_tm : S.t -> syn_tac