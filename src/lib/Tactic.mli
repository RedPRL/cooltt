module S := Syntax
module D := Domain
module EM := ElabBasics

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type bchk_tac = D.tp * D.cof * D.tm_clo -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

(** Converts a boundary-checking tactic to a checking tactic by change of base. *)
val bchk_to_chk : bchk_tac -> chk_tac

(** Converts a checking tactic to a boundary-checking tactic by a synchronous check. *)
val chk_to_bchk : chk_tac -> bchk_tac

val syn_to_chk : syn_tac -> chk_tac 
val chk_to_syn : chk_tac -> tp_tac -> syn_tac 