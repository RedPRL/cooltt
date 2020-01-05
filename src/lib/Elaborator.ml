module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module Nbe = Nbe.Monadic
module EM = ElabBasics

open CoolBasis
open Monad.Notation (EM)

let rec chk_tp : CS.t -> S.tp EM.m = 
  function
  | CS.Pi (cells, body) -> 
    chk_pi_tp cells body
  | CS.Sg (cells, body) -> 
    chk_sg_tp cells body
  | CS.Nat -> EM.ret S.Nat
  | CS.Id (tp, l, r) ->
    let* tp = chk_tp tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in 
    let+ l = chk_tm l vtp
    and+ r = chk_tm r vtp in
    S.Id (tp, l, r)
  | tp -> 
    EM.elab_err @@ Err.InvalidTypeExpression tp

and chk_tm : CS.t -> D.tp -> S.t EM.m =
  function
  | CS.Hole name ->
    Refiner.unleash_hole name
  | CS.Refl ->
    Refiner.id_intro 
  | CS.Lit n ->
    Refiner.literal n
  | CS.Lam (BN bnd) ->
    Refiner.tac_multilam bnd.names @@ chk_tm bnd.body
  | CS.Pair (c0, c1) ->
    Refiner.sg_intro (chk_tm c0) (chk_tm c1)
  | CS.Suc c ->
    Refiner.suc (chk_tm c)
  | CS.Let (c, B bdy) -> 
    Refiner.tac_let (syn_tm c) (Some bdy.name, chk_tm bdy.body)
  | cs ->
    Refiner.syn_to_chk @@ syn_tm cs

and syn_tm : CS.t -> (S.t * D.tp) EM.m = 
  function
  | CS.Var id -> 
    Refiner.lookup_var id
  | CS.Ap (t, ts) ->
    Refiner.tac_multi_apply (syn_tm t) begin
      ts |> List.map @@ fun (CS.Term cs) ->
      chk_tm cs
    end
  | CS.Fst t ->
    Refiner.pi1 @@ syn_tm t
  | CS.Snd t ->
    Refiner.pi2 @@ syn_tm t
  | CS.IdElim {mot = B3 mot; case_refl = B case_refl; scrut} ->
    Refiner.id_elim 
      (Some mot.name1, Some mot.name2, Some mot.name3, chk_tp mot.body) 
      (Some case_refl.name, chk_tm case_refl.body) 
      (syn_tm scrut)
  | CS.NatElim {mot = B mot; case_zero; case_suc = B2 case_suc; scrut} ->
    Refiner.nat_elim 
      (Some mot.name, chk_tp mot.body)
      (chk_tm case_zero)
      (Some case_suc.name1, Some case_suc.name2, chk_tm case_suc.body)
      (syn_tm scrut)
  | CS.Check {term; tp} ->
    Refiner.chk_to_syn (chk_tm term) (chk_tp tp)
  | cs -> 
    failwith @@ "TODO : " ^ CS.show cs

and chk_sg_tp cells body =
  match cells with
  | [] -> chk_tp body
  | Cell cell :: cells ->
    let* base = chk_tp cell.tp in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var (Some cell.name) vbase @@ chk_sg_tp cells body in
    S.Sg (base, fam)

and chk_pi_tp cells body =
  match cells with
  | [] -> chk_tp body
  | Cell cell :: cells ->
    let* base = chk_tp cell.tp in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var (Some cell.name) vbase @@ chk_pi_tp cells body in
    S.Pi (base, fam)