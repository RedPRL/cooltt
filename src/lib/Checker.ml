module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module R = Refiner
module EM = ElabBasics
module Err = ElabError
module T = Tactic

open CoolBasis
open Monad.Notation (EM)

exception Todo

let rec chk_tp : S.tp -> T.tp_tac =
  function
  | S.Pi (base, fam) ->
    R.Pi.formation (chk_tp base) (None, fun _ -> chk_tp fam)
  | S.Sg (base, fam) ->
    R.Sg.formation (chk_tp base) (None, fun _ -> chk_tp fam)
  | S.Id (tp, l, r) ->
    R.Id.formation (chk_tp tp) (chk_tm l) (chk_tm r)
  | S.Nat ->
    R.Nat.formation
  | S.Univ ->
    R.Univ.formation
  | S.El tm ->
    R.Univ.el_formation @@ chk_tm tm
  | S.GoalTp (lbl, tp) ->
    R.Goal.formation lbl @@ chk_tp tp
  | S.Sub (base, phi, tm) ->
    R.Sub.formation (chk_tp base) (chk_tm phi) (fun _ -> chk_tm tm)
  | S.TpDim ->
    T.Tp.make @@ EM.ret S.TpDim
  | S.TpPrf phi ->
    R.Prf.formation (chk_tm phi)
  | S.TpCof ->
    R.Cof.formation
  | S.TpVar _ ->
    failwith "Not expected"


(*

given a well-typed piece of syntax "M : A" such that [[A]] is the whnf/value of
A, then "chk_tm M [[A]]" will return a well-typed term N : A that is
judgmentally equal to M.

if the input is ill-typed, throw an error.

*)
and chk_tm : S.t -> T.chk_tac =
  function
  | S.Refl _ ->
    R.Id.intro
  | S.Zero ->
    R.Nat.literal 0
  | S.Suc t ->
    R.Nat.suc (chk_tm t)
  | S.Let (def, bdy) ->
    T.bchk_to_chk @@ R.Structural.let_ (syn_tm def) (None, fun _ -> T.chk_to_bchk @@ chk_tm bdy)
  | S.Lam bdy ->
    T.bchk_to_chk @@ R.Pi.intro None @@ fun _ -> T.chk_to_bchk @@ chk_tm bdy
  | S.Pair (t0, t1) ->
    T.bchk_to_chk @@ R.Sg.intro (T.chk_to_bchk @@ chk_tm t0) (T.chk_to_bchk @@ chk_tm t1)
  | S.CodePath (fam, bound) -> raise Todo
  | S.CodeNat ->
    R.Univ.nat
  | S.CodeSg (base, fam) ->
    R.Univ.sg (chk_tm base) (T.bchk_to_chk @@ R.Pi.intro None @@ fun _ -> T.chk_to_bchk @@ chk_tm fam)
  | S.CodePi (base, fam) ->
    R.Univ.pi (chk_tm base) (T.bchk_to_chk @@ R.Pi.intro None @@ fun _ -> T.chk_to_bchk @@ chk_tm fam)
  | t ->
    T.syn_to_chk @@ syn_tm t

and syn_tm : S.t -> T.syn_tac =
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
  | S.NatElim (mot, case_zero, case_suc, scrut) ->
    R.Nat.elim
      (None, chk_tp mot)
      (chk_tm case_zero)
      (None, None, chk_tm case_suc)
      (syn_tm scrut)
  | S.Ann (t, tp) ->
    T.chk_to_syn (chk_tm t) (chk_tp tp)
  | t ->
    EM.elab_err @@ Err.ExpectedSynthesizableTerm t
