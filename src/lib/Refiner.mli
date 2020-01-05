module D := Domain
module S := Syntax
module EM := Monads.ElabM
module CS := ConcreteSyntax

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

val unleash_hole : CS.ident option -> chk_tac
val pi_intro : CS.ident option -> chk_tac -> chk_tac
val sg_intro : chk_tac -> chk_tac -> chk_tac
val id_intro : chk_tac
val literal : int -> chk_tac
val syn_to_chk : syn_tac -> chk_tac

val lookup_var : CS.ident -> syn_tac 
val apply : syn_tac -> chk_tac -> syn_tac
val pi1 : syn_tac -> syn_tac
val pi2 : syn_tac -> syn_tac

val tac_multilam : CS.ident list -> chk_tac -> chk_tac
val tac_multi_apply : syn_tac -> chk_tac list -> syn_tac