module CS := ConcreteSyntax
module S := Syntax
module EM := Monads.ElabM
module D := Domain

open Tactic

val chk_tp : CS.con -> tp_tac
val chk_tp_in_tele : CS.cell list -> CS.con -> tp_tac
val chk_tm : CS.con -> Chk.tac
val chk_tm_in_tele : CS.cell list -> CS.con -> Chk.tac
val bchk_tm : CS.con -> BChk.tac
val syn_tm : CS.con -> Syn.tac
