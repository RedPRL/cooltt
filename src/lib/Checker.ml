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
let rec check_tp : S.tp -> R.tp_tac =
  function
  | S.Pi (base, fam) ->
    let* base = check_tp base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var None vbase @@ check_tp fam in
    S.Pi (base, fam)
  | S.Sg (base, fam) ->
    let* base = check_tp base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var None vbase @@ check_tp fam in
    S.Sg (base, fam)
  | S.Nat -> 
    EM.ret S.Nat
  | S.Id (tp, l, r) ->
    let* tp = check_tp tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in 
    let+ l = check_tm l vtp
    and+ r = check_tm r vtp in
    S.Id (tp, l, r)

and check_tm : S.t -> R.chk_tac =
  function
  | S.Refl _ ->
    Refiner.id_intro
  | S.Zero -> 
    Refiner.literal 0
  | S.Suc t ->
    Refiner.suc (check_tm t)
  | S.Let (def, bdy) ->
    Refiner.tac_let (synth_tm def) (None, check_tm bdy)
  | S.Lam bdy ->
    Refiner.pi_intro None @@ check_tm bdy
  | S.Pair (t0, t1) ->
    Refiner.sg_intro (check_tm t0) (check_tm t1)
  | t -> 
    Refiner.syn_to_chk @@ synth_tm t

and synth_tm : S.t -> R.syn_tac = 
  function
  | S.Var ix ->
    let+ tp = EM.get_local_tp ix in 
    S.Var ix, tp
  | S.Ap (t0, t1) ->
    Refiner.apply (synth_tm t0) (check_tm t1)
  | S.Fst t ->
    Refiner.pi1 @@ synth_tm t
  | S.Snd t ->
    Refiner.pi2 @@ synth_tm t
  | S.IdElim (mot, case_refl, scrut) ->
    Refiner.id_elim 
      (None, None, None, check_tp mot)
      (None, check_tm case_refl)
      (synth_tm scrut)
  | S.NatElim (mot, case_zero, case_suc, scrut) ->
    Refiner.nat_elim
      (None, check_tp mot)
      (check_tm case_zero)
      (None, None, check_tm case_suc)
      (synth_tm scrut)

  | S.Check (t, tp) -> 
    Refiner.chk_to_syn (check_tm t) (check_tp tp)

  | t -> 
    EM.elab_err @@ Err.ExpectedSynthesizableTerm t 