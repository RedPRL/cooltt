module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module R = Refiner
module Nbe = Nbe.Monadic
module EM = ElabBasics
module Err = ElabError

open CoolBasis
open Monad.Notation (EM)

(* TODO: factor into the refiner *)
let rec chk_tp : S.tp -> R.tp_tac =
  function
  | S.Pi (base, fam) ->
    let* base = chk_tp base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var None vbase @@ chk_tp fam in
    S.Pi (base, fam)
  | S.Sg (base, fam) ->
    let* base = chk_tp base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var None vbase @@ chk_tp fam in
    S.Sg (base, fam)
  | S.Nat -> 
    EM.ret S.Nat
  | S.Id (tp, l, r) ->
    let* tp = chk_tp tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in 
    let+ l = chk_tm l vtp
    and+ r = chk_tm r vtp in
    S.Id (tp, l, r)

and chk_tm : S.t -> R.chk_tac =
  function
  | S.Refl _ ->
    Refiner.id_intro
  | S.Zero -> 
    Refiner.literal 0
  | S.Suc t ->
    Refiner.suc (chk_tm t)
  | S.Let (def, bdy) ->
    Refiner.tac_let (syn_tm def) (None, chk_tm bdy)
  | S.Lam bdy ->
    Refiner.pi_intro None @@ chk_tm bdy
  | S.Pair (t0, t1) ->
    Refiner.sg_intro (chk_tm t0) (chk_tm t1)
  | t -> 
    Refiner.syn_to_chk @@ syn_tm t

and syn_tm : S.t -> R.syn_tac = 
  function
  | S.Var ix ->
    let+ tp = EM.get_local_tp ix in 
    S.Var ix, tp
  | S.Ap (t0, t1) ->
    Refiner.apply (syn_tm t0) (chk_tm t1)
  | S.Fst t ->
    Refiner.pi1 @@ syn_tm t
  | S.Snd t ->
    Refiner.pi2 @@ syn_tm t
  | S.IdElim (mot, case_refl, scrut) ->
    Refiner.id_elim 
      (None, None, None, chk_tp mot)
      (None, chk_tm case_refl)
      (syn_tm scrut)
  | S.NatElim (mot, case_zero, case_suc, scrut) ->
    Refiner.nat_elim
      (None, chk_tp mot)
      (chk_tm case_zero)
      (None, None, chk_tm case_suc)
      (syn_tm scrut)

  | S.Check (t, tp) -> 
    Refiner.chk_to_syn (chk_tm t) (chk_tp tp)

  | t -> 
    EM.elab_err @@ Err.ExpectedSynthesizableTerm t 