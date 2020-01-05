module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module Nbe = Nbe.Monadic
module EM = ElabBasics

open CoolBasis
open Monad.Notation (EM)

let rec check_tp : CS.t -> S.tp EM.m = 
  function
  | CS.Pi (cells, body) -> 
    check_pi_tp cells body
  | CS.Sg (cells, body) -> 
    check_sg_tp cells body
  | CS.Nat -> EM.ret S.Nat
  | CS.Id (tp, l, r) ->
    let* tp = check_tp tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in 
    let+ l = check_tm l vtp
    and+ r = check_tm r vtp in
    S.Id (tp, l, r)
  | tp -> 
    EM.elab_err @@ Err.InvalidTypeExpression tp

and check_tm : CS.t -> D.tp -> S.t EM.m =
  function
  | CS.Hole name ->
    Refiner.unleash_hole name
  | CS.Refl ->
    Refiner.id_intro 
  | CS.Lit n ->
    Refiner.literal n
  | CS.Lam (BN bnd) ->
    Refiner.tac_multilam bnd.names @@ check_tm bnd.body
  | CS.Pair (c0, c1) ->
    Refiner.sg_intro (check_tm c0) (check_tm c1)
  | cs ->
    Refiner.syn_to_chk @@ synth_tm cs

and synth_tm : CS.t -> (S.t * D.tp) EM.m = 
  function
  | CS.Var id -> 
    Refiner.lookup_var id
  | CS.Ap (t, ts) ->
    Refiner.tac_multi_apply (synth_tm t) begin
      ts |> List.map @@ fun (CS.Term cs) ->
      check_tm cs
    end
  | CS.Fst t ->
    Refiner.pi1 @@ synth_tm t
  | CS.Snd t ->
    Refiner.pi2 @@ synth_tm t
  | CS.J {mot = B3 mot; case_refl = B case_refl; scrut} ->
    Refiner.id_elim 
      (mot.name1, mot.name2, mot.name3, check_tp mot.body) 
      (case_refl.name, check_tm case_refl.body) 
      (synth_tm scrut)
  | cs -> 
    failwith @@ "TODO : " ^ CS.show cs

and check_sg_tp cells body =
  match cells with
  | [] -> check_tp body
  | Cell cell :: cells ->
    let* base = check_tp cell.tp in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var (Some cell.name) vbase @@ check_sg_tp cells body in
    S.Sg (base, fam)

and check_pi_tp cells body =
  match cells with
  | [] -> check_tp body
  | Cell cell :: cells ->
    let* base = check_tp cell.tp in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var (Some cell.name) vbase @@ check_pi_tp cells body in
    S.Pi (base, fam)