module S = Syntax
module D = Domain
module EM = ElabBasics

open CoolBasis
open Monad.Notation (EM)

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
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