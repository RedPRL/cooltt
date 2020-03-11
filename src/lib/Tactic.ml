module S = Syntax
module D = Domain
module EM = ElabBasics

open CoolBasis
open Monad.Notation (EM)

type tp_tac = S.tp EM.m
type 'a chk_tac_ = D.tp -> 'a EM.m
type chk_tac = S.t chk_tac_ 
type bchk_tac = D.tp * D.cof * S.t D.pclo -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m 

let bchk_to_chk : bchk_tac -> chk_tac =
  fun btac tp -> 
  let triv = D.PCloConst D.Abort in
  btac (tp, Cof.bot, triv)


let chk_to_bchk : chk_tac -> bchk_tac = 
  fun tac (tp, phi, pclo) ->
  let* tm = tac tp in
  let* con = EM.lift_ev @@ Nbe.eval tm in
  let* () = 
    EM.push_var None (D.Tp (D.TpPrf phi)) @@
    EM.equate tp con @<< EM.lift_cmp @@ Nbe.inst_pclo pclo
  in
  EM.ret tm  

let syn_to_chk (tac : syn_tac) : chk_tac =
  fun tp ->
  let* tm, tp' = tac in
  let+ () = EM.equate_tp tp tp' in
  tm

let chk_to_syn (tac_tm : chk_tac) (tac_tp : tp_tac) : syn_tac =
  let* tp = tac_tp in
  let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
  let+ tm = tac_tm vtp in
  tm, vtp
