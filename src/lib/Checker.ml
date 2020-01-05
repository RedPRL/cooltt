module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module R = Refiner
module Nbe = Nbe.Monadic
module EM = ElabBasics
module Err = ElabError

open CoolBasis
open Monad.Notation (EM)

let rec chk_tp : S.tp -> R.tp_tac =
  function
  | S.Pi (base, fam) ->
    R.pi_formation (chk_tp base) (None, chk_tp fam)
  | S.Sg (base, fam) ->
    R.sg_formation (chk_tp base) (None, chk_tp fam)
  | S.Id (tp, l, r) ->
    R.id_formation (chk_tp tp)(chk_tm l) (chk_tm r)
  | S.Nat -> 
    EM.ret S.Nat

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