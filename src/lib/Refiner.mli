module D := Domain
module S := Syntax
module EM := Monads.ElabM
module CS := ConcreteSyntax

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

val unleash_hole : CS.ident option -> chk_tac

val pi_formation : tp_tac -> CS.ident option * tp_tac -> tp_tac
val sg_formation : tp_tac -> CS.ident option * tp_tac -> tp_tac
val id_formation : tp_tac -> chk_tac -> chk_tac -> tp_tac

val pi_intro : CS.ident option -> chk_tac -> chk_tac
val sg_intro : chk_tac -> chk_tac -> chk_tac
val id_intro : chk_tac

val literal : int -> chk_tac
val suc : chk_tac -> chk_tac
val syn_to_chk : syn_tac -> chk_tac
val chk_to_syn : chk_tac -> tp_tac -> syn_tac

val tac_let : syn_tac -> CS.ident option * chk_tac -> chk_tac 

val lookup_var : CS.ident -> syn_tac 
val apply : syn_tac -> chk_tac -> syn_tac
val pi1 : syn_tac -> syn_tac
val pi2 : syn_tac -> syn_tac

val id_elim 
  : (CS.ident option * CS.ident option * CS.ident option * tp_tac) 
  -> (CS.ident option * chk_tac) 
  -> syn_tac 
  -> syn_tac

val nat_elim 
  : (CS.ident option * tp_tac)
  -> chk_tac
  -> (CS.ident option * CS.ident option * chk_tac)
  -> syn_tac
  -> syn_tac

val tac_multilam : CS.ident list -> chk_tac -> chk_tac
val tac_multi_apply : syn_tac -> chk_tac list -> syn_tac