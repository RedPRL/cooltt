module CS := ConcreteSyntax
module S := Syntax
module EM := Monads.ElabM
module D := Domain

open Tactic

val chk_tp : CS.t -> tp_tac
val chk_tm : CS.t -> chk_tac
val bchk_tm : CS.t -> bchk_tac
val syn_tm : CS.t -> syn_tac
