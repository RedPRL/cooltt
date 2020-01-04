module D := Domain
module S := Syntax
module EM := ElabMonad
module CS := ConcreteSyntax

type tp_tac = D.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

val eval_tp : S.tp -> D.tp EM.m
val eval_tm : S.t -> D.t EM.m
val inst_tp_clo : (S.tp, D.tp) D.clo -> D.t -> D.tp EM.m
val equate_tp : D.tp -> D.tp -> unit EM.m
val dest_pi : D.tp -> (D.tp * (S.tp, D.tp) D.clo) EM.m


val unleash_hole : CS.ident option -> chk_tac
val pi_intro : CS.ident option -> chk_tac -> chk_tac
val sg_intro : chk_tac -> chk_tac -> chk_tac
val id_intro : chk_tac
val literal : int -> chk_tac
val syn_to_chk : syn_tac -> chk_tac

val lookup_var : CS.ident -> syn_tac 
val apply : syn_tac -> chk_tac -> syn_tac

val tac_multilam : CS.ident list -> chk_tac -> chk_tac
val tac_multi_apply : syn_tac -> chk_tac list -> syn_tac