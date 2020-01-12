module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module R = Refiner
module EM = ElabBasics
module Err = ElabError

open CoolBasis
open Monad.Notation (EM)

let rec chk_tp : S.tp -> R.tp_tac =
  function
  | S.Pi (base, fam) ->
    R.Pi.formation (chk_tp base) (None, chk_tp fam)
  | S.Sg (base, fam) ->
    R.Sg.formation (chk_tp base) (None, chk_tp fam)
  | S.Id (tp, l, r) ->
    R.Id.formation (chk_tp tp)(chk_tm l) (chk_tm r)
  | S.Nat -> 
    EM.ret S.Nat
  | S.Univ -> 
    EM.ret S.Univ
  | S.El tm ->
    R.El.formation @@ chk_tm tm
  | S.GoalTp (lbl, tp) ->
    R.Goal.formation lbl @@ chk_tp tp

and chk_tm : S.t -> R.chk_tac =
  function
  | S.Refl _ ->
    R.Id.intro
  | S.Zero -> 
    R.Nat.literal 0
  | S.Suc t ->
    R.Nat.suc (chk_tm t)
  | S.Let (def, bdy) ->
    R.Structural.let_ (syn_tm def) (None, chk_tm bdy)
  | S.Lam bdy ->
    R.Pi.intro None @@ chk_tm bdy
  | S.Pair (t0, t1) ->
    R.Sg.intro (chk_tm t0) (chk_tm t1)
  | t -> 
    R.Structural.syn_to_chk @@ syn_tm t

and syn_tm : S.t -> R.syn_tac = 
  function
  | S.Var ix ->
    let+ tp = EM.get_local_tp ix in 
    S.Var ix, tp
  | S.Ap (t0, t1) ->
    R.Pi.apply (syn_tm t0) (chk_tm t1)
  | S.Fst t ->
    R.Sg.pi1 @@ syn_tm t
  | S.Snd t ->
    R.Sg.pi2 @@ syn_tm t
  | S.IdElim (mot, case_refl, scrut) ->
    R.Id.elim 
      (None, None, None, chk_tp mot)
      (None, chk_tm case_refl)
      (syn_tm scrut)
  | S.NatElim (_, mot, case_zero, case_suc, scrut) ->
    R.Nat.elim
      (None, chk_tp mot)
      (chk_tm case_zero)
      (None, None, chk_tm case_suc)
      (syn_tm scrut)
  | S.Ann (t, tp) -> 
    R.Structural.chk_to_syn (chk_tm t) (chk_tp tp)
  | t -> 
    EM.elab_err @@ Err.ExpectedSynthesizableTerm t 