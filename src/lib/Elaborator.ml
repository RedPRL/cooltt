module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module R = Refiner
module T = Tactic

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

let rec chk_tp : CS.t -> T.tp_tac = 
  function
  | CS.Hole name ->
    R.Hole.unleash_tp_hole name `Rigid
  | CS.Underscore -> 
    R.Hole.unleash_tp_hole None `Flex
  | CS.Pi (cells, body) -> 
    let tac (CS.Cell cell) = Some cell.name, chk_tp cell.tp in
    let tacs = cells |> List.map tac in 
    R.Tactic.tac_nary_quantifier R.Pi.formation tacs @@ chk_tp body
  | CS.Sg (cells, body) -> 
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> Some cell.name, chk_tp cell.tp in
    R.Tactic.tac_nary_quantifier R.Sg.formation tacs @@ chk_tp body
  | CS.Id (tp, l, r) ->
    R.Id.formation (chk_tp tp) (chk_tm l) (chk_tm r)
  | CS.Nat -> 
    R.Nat.formation
  | CS.Univ ->
    R.Univ.formation
  | CS.Unfold (idents, c) -> 
    T.Tp.map (unfold idents) @@ chk_tp c
  | CS.Dim ->
    R.Dim.formation
  | CS.Cof ->
    R.Cof.formation
  | CS.Prf phi ->
    R.Prf.formation @@ chk_tm phi
  | CS.Sub (ctp, cphi, ctm) ->
    R.Sub.formation (chk_tp ctp) (chk_tm cphi) (chk_tm ctm)
  | tm -> 
    Refiner.Univ.el_formation @@ chk_tm tm

and chk_tm : CS.t -> T.chk_tac = 
  fun cs ->
  T.bchk_to_chk @@ bchk_tm cs


and bchk_tm : CS.t -> T.bchk_tac = 
  fun cs ->
  R.Tactic.bmatch_goal @@ function
  | D.Sub _, _, _ ->
    EM.ret @@ R.Sub.intro (bchk_tm cs)
  | _ -> 
    EM.ret @@ bchk_tm_ cs 

and bchk_tm_ : CS.t -> T.bchk_tac = 
  function
  | CS.Hole name ->
    R.Hole.unleash_hole name `Rigid
  | CS.Underscore -> 
    R.Prf.intro
  (* R.Hole.unleash_hole None `Flex *)
  | CS.Refl ->
    T.chk_to_bchk @@ R.Id.intro 
  | CS.Lit n ->
    begin
      T.chk_to_bchk @@ 
      R.Tactic.match_goal @@ function
      | D.TpDim -> EM.ret @@ R.Dim.literal n
      | _ -> EM.ret @@ R.Nat.literal n
    end
  | CS.Lam (BN bnd) ->
    R.Tactic.tac_multi_lam bnd.names @@ bchk_tm bnd.body
  | CS.LamElim cases ->
    T.chk_to_bchk @@ R.Tactic.Elim.lam_elim @@ chk_cases cases
  | CS.Pair (c0, c1) ->
    R.Sg.intro (bchk_tm c0) (bchk_tm c1)
  | CS.Suc c ->
    T.chk_to_bchk @@ R.Nat.suc (chk_tm c)
  | CS.Let (c, B bdy) -> 
    R.Structural.let_ (syn_tm c) (Some bdy.name, bchk_tm bdy.body)
  | CS.Unfold (idents, c) -> 
    fun goal ->
      unfold idents @@ bchk_tm c goal
  | CS.Nat ->
    T.chk_to_bchk @@ R.Univ.nat
  | CS.Pi (cells, body) ->
    let tac (CS.Cell cell) =  Some cell.name, chk_tm cell.tp in
    let tacs = cells |> List.map tac in 
    T.chk_to_bchk @@ R.Tactic.tac_nary_quantifier R.Univ.pi tacs @@ chk_tm body
  | CS.Sg (cells, body) ->
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> Some cell.name, chk_tm cell.tp in
    T.chk_to_bchk @@ R.Tactic.tac_nary_quantifier R.Univ.sg tacs @@ chk_tm body
  | CS.Id (tp, l, r) ->
    T.chk_to_bchk @@ R.Univ.id (chk_tm tp) (chk_tm l) (chk_tm r)
  | CS.CofEq (c0, c1) ->
    T.chk_to_bchk @@ R.Cof.eq (chk_tm c0) (chk_tm c1)
  | CS.Join (c0, c1) ->
    T.chk_to_bchk @@ R.Cof.join (chk_tm c0) (chk_tm c1)
  | CS.Meet (c0, c1) ->
    T.chk_to_bchk @@ R.Cof.meet (chk_tm c0) (chk_tm c1)
  | CS.CofSplit splits ->
    let branch_tacs = splits |> List.map @@ fun (cphi, ctm) -> chk_tm cphi, bchk_tm ctm in 
    R.Cof.split branch_tacs
  | cs ->
    T.chk_to_bchk @@ T.syn_to_chk @@ syn_tm cs


and syn_tm_ : CS.t -> T.syn_tac = 
  function
  | CS.Hole name ->
    R.Hole.unleash_syn_hole name `Rigid
  | CS.Var id -> 
    R.Structural.lookup_var id
  | CS.Ap (t, ts) ->
    R.Tactic.tac_multi_apply (syn_tm t) @@ List.map chk_tm ts
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
    T.chk_to_syn (chk_tm term) (chk_tp tp)
  | CS.Unfold (idents, c) -> 
    unfold idents @@ syn_tm c
  | cs -> 
    failwith @@ "TODO : " ^ CS.show cs

and syn_tm : CS.t -> T.syn_tac =
  fun c -> 
  let* tm, tp = syn_tm_ c in 
  match tp with 
  | D.Sub (tp, _, _) ->
    EM.ret (S.SubOut tm, tp)
  | _ -> 
    EM.ret (tm, tp)

and chk_cases cases =
  List.map chk_case cases

and chk_case (pat, c) =
  pat, chk_tm c