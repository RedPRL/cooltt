module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module R = Refiner

open CoolBasis
open Monad.Notation (EM)

let rec unfold idents k =
  match idents with 
  | [] -> k
  | ident :: idents ->
    let* res = EM.resolve ident in
    match res with
    | `Global sym ->
      let* env = EM.read in
      let veil = Veil.unfold [sym] @@ Env.get_veil env in
      EM.veil veil @@ unfold idents k
    | _ -> 
      unfold idents k

let rec chk_tp : CS.t -> S.tp EM.m = 
  function
  | CS.Hole name ->
    R.Hole.unleash_tp_hole name `Rigid
  | CS.Underscore -> 
    R.Hole.unleash_tp_hole None `Flex
  | CS.Pi (cells, body) -> 
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> Some cell.name, chk_tp cell.tp in
    R.Tactic.tac_nary_quantifier R.Pi.formation tacs @@ chk_tp body
  | CS.Sg (cells, body) -> 
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> Some cell.name, chk_tp cell.tp in
    R.Tactic.tac_nary_quantifier R.Sg.formation tacs @@ chk_tp body
  | CS.Id (tp, l, r) ->
    R.Id.formation (chk_tp tp) (chk_tm l) (chk_tm r)
  | CS.Nat -> 
    EM.ret S.Nat
  | CS.Univ ->
    R.Univ.formation
  | CS.Unfold (idents, c) -> 
    unfold idents @@ chk_tp c
  | tm -> 
    Refiner.Univ.el_formation @@ chk_tm tm

and chk_tm : CS.t -> D.tp -> S.t EM.m =
  function
  | CS.Hole name ->
    R.Hole.unleash_hole name `Rigid
  | CS.Underscore -> 
    R.Hole.unleash_hole None `Flex
  | CS.Refl ->
    R.Id.intro 
  | CS.Lit n ->
    R.Nat.literal n
  | CS.Lam (BN bnd) ->
    R.Tactic.tac_multi_lam bnd.names @@ chk_tm bnd.body
  | CS.LamElim cases ->
    R.Tactic.Elim.lam_elim @@ chk_cases cases
  | CS.Pair (c0, c1) ->
    R.Sg.intro (chk_tm c0) (chk_tm c1)
  | CS.Suc c ->
    R.Nat.suc (chk_tm c)
  | CS.Let (c, B bdy) -> 
    R.Structural.let_ (syn_tm c) (Some bdy.name, chk_tm bdy.body)
  | CS.Unfold (idents, c) -> 
    fun tp ->
      unfold idents @@ chk_tm c tp
  | CS.Nat ->
    R.Univ.nat
  | CS.Pi (cells, body) ->
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> Some cell.name, chk_tm cell.tp in
    R.Tactic.tac_nary_quantifier R.Univ.pi tacs @@ chk_tm body
  | cs ->
    R.Structural.syn_to_chk @@ syn_tm cs

and syn_tm : CS.t -> (S.t * D.tp) EM.m = 
  function
  | CS.Hole name ->
    R.Hole.unleash_syn_hole name `Rigid
  | CS.Var id -> 
    R.Structural.lookup_var id
  | CS.Ap (t, ts) ->
    R.Tactic.tac_multi_apply (syn_tm t) begin
      ts |> List.map @@ fun (CS.Term cs) ->
      chk_tm cs
    end
  | CS.Fst t ->
    R.Sg.pi1 @@ syn_tm t
  | CS.Snd t ->
    R.Sg.pi2 @@ syn_tm t
  | CS.Elim {mot = BN mot; cases; scrut} ->
    let names = List.map (fun x -> Some x) mot.names in
    R.Tactic.Elim.elim 
      (names, chk_tp mot.body) 
      (chk_cases cases)
      (syn_tm scrut)
  | CS.Ann {term; tp} ->
    R.Structural.chk_to_syn (chk_tm term) (chk_tp tp)
  | CS.Unfold (idents, c) -> 
    unfold idents @@ syn_tm c
  | cs -> 
    failwith @@ "TODO : " ^ CS.show cs

and chk_cases cases =
  List.map chk_case cases

and chk_case (pat, c) =
  pat, chk_tm c