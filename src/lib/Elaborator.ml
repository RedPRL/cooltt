module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError

module EM = ElabBasics
open Monad.Notation (EM)

let rec check_tp : CS.t -> S.tp EM.m = 
  function
  | CS.Pi (cells, body) -> check_pi_tp cells body
  | CS.Sg (cells, body) -> check_sg_tp cells body
  | CS.Nat -> EM.ret S.Nat
  | CS.Id (tp, l, r) ->
    let* tp = check_tp tp in
    let* vtp = EM.lift_ev @@ Nbe.Monadic.eval_tp tp in 
    let+ l = check_tm l vtp
    and+ r = check_tm r vtp in
    S.Id (tp, l, r)
  | tp -> EM.throw @@ Err.ElabError (Err.InvalidTypeExpression tp)

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
  | cs ->
    Refiner.syn_to_chk @@ synth_tm cs

and synth_tm : CS.t -> (S.t * D.tp) EM.m = 
  function
  | CS.Var id -> Refiner.lookup_var id
  | CS.Ap (t, ts) ->
    Refiner.tac_multi_apply (synth_tm t) begin
      ts |> List.map @@ fun (CS.Term cs) ->
      check_tm cs
    end
  | cs -> 
    failwith @@ "TODO : " ^ CS.show cs

and check_sg_tp cells body =
  match cells with
  | [] -> check_tp body
  | Cell cell :: cells ->
    let* base = check_tp cell.tp in
    let* vbase = EM.lift_ev @@ Nbe.Monadic.eval_tp base in
    let+ fam = EM.push_var (Some cell.name) vbase @@ check_sg_tp cells body in
    S.Sg (base, fam)

and check_pi_tp cells body =
  match cells with
  | [] -> check_tp body
  | Cell cell :: cells ->
    let* base = check_tp cell.tp in
    let* vbase = EM.lift_ev @@ Nbe.Monadic.eval_tp base in
    let+ fam = EM.push_var (Some cell.name) vbase @@ check_pi_tp cells body in
    S.Pi (base, fam)