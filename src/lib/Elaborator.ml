module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module R = Refiner
module T = Tactic
module Sem = Semantics

open CoolBasis
open Monad.Notation (EM)

exception Todo

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

let whnf_chk tac =
  fun goal ->
  EM.lift_cmp @@ Sem.whnf_tp goal |>>
  function
  | `Done -> tac goal
  | `Reduce goal -> tac goal

let whnf_bchk (tac : T.bchk_tac) : T.bchk_tac =
  fun (tp, psi, clo) ->
  EM.lift_cmp @@ Sem.whnf_tp tp |>>
  function
  | `Done -> tac (tp, psi, clo)
  | `Reduce tp -> tac (tp, psi, clo)

let rec chk_tp : CS.con -> T.tp_tac =
  fun con ->
  T.Tp.update_span con.info @@
  match con.node with
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
    R.Sub.formation (chk_tp ctp) (chk_tm cphi) (fun _ -> chk_tm ctm)
  | _ ->
    Refiner.El.formation @@ chk_tm con

and chk_tm : CS.con -> T.chk_tac =
  fun con ->
  T.Chk.bchk @@ bchk_tm con

and bchk_tm : CS.con -> T.bchk_tac =
  fun con ->
  T.BChk.update_span con.info @@
  R.Tactic.intro_implicit_connectives @@
  whnf_bchk @@
  match con.node with
  | CS.Hole name ->
    R.Hole.unleash_hole name `Rigid
  | CS.Underscore ->
    R.Prf.intro
  (* R.Hole.unleash_hole None `Flex *)
  | CS.Lit n ->
    begin
      T.BChk.chk @@
      R.Tactic.match_goal @@ function
      | D.TpDim -> EM.ret @@ R.Dim.literal n
      | _ -> EM.ret @@ R.Nat.literal n
    end
  | CS.Lam (BN bnd) ->
    R.Tactic.tac_multi_lam bnd.names @@ bchk_tm bnd.body
  | CS.LamElim cases ->
    R.Tactic.Elim.lam_elim @@ chk_cases cases
  | CS.Pair (c0, c1) ->
    R.Sg.intro (bchk_tm c0) (bchk_tm c1)
  | CS.Suc c ->
    T.BChk.chk @@ R.Nat.suc (chk_tm c)
  | CS.Let (c, B bdy) ->
    R.Structural.let_ (syn_tm c) (Some bdy.name, fun _ -> bchk_tm bdy.body)
  | CS.Unfold (idents, c) ->
    fun goal ->
      unfold idents @@ bchk_tm c goal
  | CS.Nat ->
    T.BChk.chk R.Univ.nat
  | CS.Pi (cells, body) ->
    let tac (CS.Cell cell) =  Some cell.name, chk_tm cell.tp in
    let tacs = cells |> List.map tac in
    let quant base (nm, fam) = R.Univ.pi base (T.Chk.bchk @@ R.Pi.intro nm @@ fun var -> T.BChk.chk (fam var)) in
    T.BChk.chk @@ R.Tactic.tac_nary_quantifier quant tacs @@ chk_tm body
  | CS.Sg (cells, body) ->
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> Some cell.name, chk_tm cell.tp in
    let quant base (nm, fam) = R.Univ.sg base (T.Chk.bchk @@ R.Pi.intro nm @@ fun var -> T.BChk.chk (fam var)) in
    T.BChk.chk @@ R.Tactic.tac_nary_quantifier quant tacs @@ chk_tm body
  | CS.CofEq (c0, c1) ->
    T.BChk.chk @@ R.Cof.eq (chk_tm c0) (chk_tm c1)
  | CS.Join cs ->
    T.BChk.chk @@ R.Cof.join (List.map chk_tm cs)
  | CS.Meet cs ->
    T.BChk.chk @@ R.Cof.meet (List.map chk_tm cs)
  | CS.CofBoundary c ->
    T.BChk.chk @@ R.Cof.boundary (chk_tm c)
  | CS.CofSplit splits ->
    let branch_tacs = splits |> List.map @@ fun (cphi, ctm) -> chk_tm cphi, fun _ -> bchk_tm ctm in
    R.Cof.split branch_tacs
  | CS.Path (tp, a, b) ->
    T.BChk.chk @@ R.Univ.path_with_endpoints (chk_tm tp) (bchk_tm a) (bchk_tm b)
  | CS.AutoHCom (tp, r, s, bdy) ->
    R.Univ.auto_hcom (chk_tm tp) (chk_tm r) (chk_tm s) (chk_tm bdy)
  | _ ->
    R.Tactic.bmatch_goal @@ fun (tp, _, _) ->
    match tp with
    | D.Pi _ ->
      let* env = EM.read in
      let lvl = ElabEnv.size env in
      EM.ret @@ R.Pi.intro None @@ fun _ -> bchk_tm @@ CS.{node = CS.Ap (con, [CS.{node = Var (`Level lvl); info = None}]); info = None}
    | D.Sg _ ->
      EM.ret @@ R.Sg.intro (bchk_tm @@ CS.{node = CS.Fst con; info = None}) (bchk_tm @@ CS.{node = CS.Snd con; info = None})
    | _ ->
      EM.ret @@ T.BChk.syn @@ syn_tm con

and syn_tm : CS.con -> T.syn_tac =
  function con ->
  T.Syn.update_span con.info @@
  R.Tactic.elim_implicit_connectives @@
  match con.node with
  | CS.Hole name ->
    R.Hole.unleash_syn_hole name `Rigid
  | CS.Var (`User id) ->
    R.Structural.lookup_var id
  | CS.Var (`Level lvl) ->
    R.Structural.level lvl
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
    T.Syn.ann (chk_tm term) (chk_tp tp)
  | CS.Unfold (idents, c) ->
    unfold idents @@ syn_tm c
  | CS.Coe (tp, src, trg, body) ->
    R.Univ.coe (chk_tm tp) (chk_tm src) (chk_tm trg) (chk_tm body)
  | CS.HCom (tp, src, trg, cof, tm) ->
    R.Univ.hcom (chk_tm tp) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
  | CS.Com (fam, src, trg, cof, tm) ->
    R.Univ.com (chk_tm fam) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
  | CS.TopC -> R.Univ.topc
  | CS.BotC -> R.Univ.botc
  | _ ->
    failwith @@ "TODO : " ^ CS.show_con con

and chk_cases cases =
  List.map chk_case cases

and chk_case (pat, c) =
  pat, chk_tm c
