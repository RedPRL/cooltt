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

let whnf_syn (tac : T.syn_tac) =
  let* tm, tp = tac in
  EM.lift_cmp @@ Sem.whnf_tp tp |>>
  function
  | `Done -> EM.ret (tm, tp)
  | `Reduce tp' -> EM.ret (tm, tp')

let whnf_bchk (tac : T.bchk_tac) : T.bchk_tac =
  fun (tp, psi, clo) ->
  EM.lift_cmp @@ Sem.whnf_tp tp |>>
  function
  | `Done -> tac (tp, psi, clo)
  | `Reduce tp -> tac (tp, psi, clo)


module CoolTp :
sig
  include T.Tactic

  val as_tp : tac -> T.Tp.tac
  val pi : tac -> Ident.t -> tac -> tac
  val sg : tac -> Ident.t -> tac -> tac
  val sub : tac -> T.Chk.tac -> T.Chk.tac -> tac
  val path : T.Chk.tac -> T.Chk.tac -> T.Chk.tac -> tac
  val nat : tac
  val univ : tac
  val dim : tac
  val cof : tac
  val prf : T.Chk.tac -> tac

  val code : T.Chk.tac -> tac
end =
struct
  type tac =
    | Tp of T.Tp.tac
    | Code of T.Chk.tac

  let update_span span =
    function
    | Tp tac -> Tp (T.Tp.update_span span tac)
    | Code tac -> Code (T.Chk.update_span span tac)

  let as_tp =
    function
    | Tp tac -> tac
    | Code tac -> R.El.formation tac

  let pi (tac_base : tac) (ident : Ident.t) (tac_fam : tac) : tac =
    match tac_base, tac_fam with
    | Code tac_base, Code tac_fam ->
      let tac = R.Univ.pi tac_base @@ T.Chk.bchk @@ R.Pi.intro ~ident @@ fun _ -> T.BChk.chk tac_fam in
      Code tac
    | _ ->
      let tac_base = as_tp tac_base in
      let tac_fam = as_tp tac_fam in
      let tac = R.Pi.formation tac_base (ident, fun _ -> tac_fam) in
      Tp tac

  let sg (tac_base : tac) (ident : Ident.t) (tac_fam : tac) : tac =
    match tac_base, tac_fam with
    | Code tac_base, Code tac_fam ->
      let tac = R.Univ.sg tac_base @@ T.Chk.bchk @@ R.Pi.intro ~ident @@ fun _ -> T.BChk.chk tac_fam in
      Code tac
    | _ ->
      let tac_base = as_tp tac_base in
      let tac_fam = as_tp tac_fam in
      let tac = R.Sg.formation tac_base (ident, fun _ -> tac_fam) in
      Tp tac

  let sub tac_tp tac_phi tac_pel : tac =
    let tac = R.Sub.formation (as_tp tac_tp) tac_phi (fun _ -> tac_pel) in
    Tp tac

  let path tac_tp tac_l tac_r =
    let tac = R.Univ.path_with_endpoints tac_tp (T.BChk.chk tac_l) (T.BChk.chk tac_r) in
    Code tac

  let nat = Code R.Univ.nat
  let univ = Code R.Univ.univ
  let dim = Tp R.Dim.formation
  let cof = Tp R.Cof.formation
  let prf tac = Tp (R.Prf.formation tac)
  let code tac = Code tac
end

let rec cool_chk_tp : CS.con -> CoolTp.tac =
  fun con ->
  CoolTp.update_span con.info @@
  match con.node with
  | CS.Pi ([], body) ->
    cool_chk_tp body
  | CS.Pi (CS.Cell cell :: cells, body) ->
    CoolTp.pi (cool_chk_tp cell.tp) cell.name @@
    cool_chk_tp {con with node = CS.Pi (cells, body)}
  | CS.Sg ([], body) ->
    cool_chk_tp body
  | CS.Sg (CS.Cell cell :: cells, body) ->
    CoolTp.sg (cool_chk_tp cell.tp) cell.name @@
    cool_chk_tp {con with node = CS.Sg (cells, body)}
  | CS.Dim -> CoolTp.dim
  | CS.Cof -> CoolTp.cof
  | CS.Prf phi -> CoolTp.prf @@ chk_tm phi
  | CS.Sub (ctp, cphi, ctm) -> CoolTp.sub (cool_chk_tp ctp) (chk_tm cphi) (chk_tm ctm)
  | CS.Path (tp, a, b) -> CoolTp.path (chk_tm tp) (chk_tm a) (chk_tm b)
  | _ -> CoolTp.code @@ chk_tm con


and chk_tp : CS.con -> T.tp_tac =
  fun con ->
  T.Tp.update_span con.info @@
  CoolTp.as_tp @@ cool_chk_tp con

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

  | CS.Lam (BN {names = []; body}) ->
    bchk_tm body

  | CS.Lam (BN {names = nm :: names; body}) ->
    R.Pi.intro ~ident:nm @@ fun _ ->
    bchk_tm {con with node = CS.Lam (BN {names; body})}

  | CS.LamElim cases ->
    R.Tactic.Elim.lam_elim @@ chk_cases cases
  | CS.Pair (c0, c1) ->
    R.Sg.intro (bchk_tm c0) (bchk_tm c1)
  | CS.Suc c ->
    T.BChk.chk @@ R.Nat.suc (chk_tm c)
  | CS.Let (c, B bdy) ->
    R.Structural.let_ ~ident:bdy.name (syn_tm c) @@ fun _ -> bchk_tm bdy.body
  | CS.Unfold (idents, c) ->
    fun goal ->
      unfold idents @@ bchk_tm c goal
  | CS.Nat ->
    T.BChk.chk R.Univ.nat
  | CS.Type ->
    T.BChk.chk R.Univ.univ
  | CS.Pi (cells, body) ->
    let tac (CS.Cell cell) = cell.name, chk_tm cell.tp in
    let tacs = cells |> List.map tac in
    let quant base (nm, fam) = R.Univ.pi base (T.Chk.bchk @@ R.Pi.intro ~ident:nm @@ fun var -> T.BChk.chk (fam var)) in
    T.BChk.chk @@ R.Tactic.tac_nary_quantifier quant tacs @@ chk_tm body
  | CS.Sg (cells, body) ->
    let tacs = cells |> List.map @@ fun (CS.Cell cell) -> cell.name, chk_tm cell.tp in
    let quant base (nm, fam) = R.Univ.sg base (T.Chk.bchk @@ R.Pi.intro ~ident:nm @@ fun var -> T.BChk.chk (fam var)) in
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
  | CS.HFill (tp, src, cof, tm) ->
    R.Pi.intro ~ident:(`Machine "i") @@ fun i ->
    R.Tactic.intro_implicit_connectives @@
    T.BChk.syn @@
    R.Tactic.elim_implicit_connectives @@
    R.Univ.hcom (chk_tm tp) (chk_tm src) (T.Chk.syn @@ T.Var.syn i) (chk_tm cof) (chk_tm tm)
  | _ ->
    R.Tactic.bmatch_goal @@ fun (tp, _, _) ->
    match tp with
    | D.Pi _ ->
      let* env = EM.read in
      let lvl = ElabEnv.size env in
      EM.ret @@ R.Pi.intro @@ fun _ -> bchk_tm @@ CS.{node = CS.Ap (con, [CS.{node = DeBruijnLevel lvl; info = None}]); info = None}
    | D.Sg _ ->
      EM.ret @@ R.Sg.intro (bchk_tm @@ CS.{node = CS.Fst con; info = None}) (bchk_tm @@ CS.{node = CS.Snd con; info = None})
    | _ ->
      EM.ret @@ T.BChk.syn @@ syn_tm con

and syn_tm : CS.con -> T.syn_tac =
  function con ->
    T.Syn.update_span con.info @@
    whnf_syn @@
    R.Tactic.elim_implicit_connectives @@
    whnf_syn @@
    match con.node with
    | CS.Hole name ->
      R.Hole.unleash_syn_hole name `Rigid
    | CS.Var id ->
      R.Structural.lookup_var id
    | CS.DeBruijnLevel lvl ->
      R.Structural.level lvl
    | CS.Ap (t, []) ->
      syn_tm t
    | CS.Ap (t, ts) ->
      let rec go acc ts =
        match ts with
        | [] -> acc
        | t :: ts ->
          let tac = R.Tactic.elim_implicit_connectives @@ whnf_syn @@ R.Pi.apply acc t in
          go tac ts
      in
      go (syn_tm t) @@ List.map chk_tm ts
    | CS.Fst t ->
      R.Sg.pi1 @@ syn_tm t
    | CS.Snd t ->
      R.Sg.pi2 @@ syn_tm t
    | CS.Elim {mot; cases; scrut} ->
      R.Tactic.Elim.elim
        (chk_tm mot)
        (chk_cases cases)
        (syn_tm scrut)
    | CS.Rec {mot; cases; scrut} ->
      let mot_tac = chk_tm mot in
      R.Structural.let_syn (T.Syn.ann mot_tac R.Univ.formation) @@ fun tp ->
      R.Tactic.Elim.elim
        (T.Chk.bchk @@ R.Pi.intro @@ fun _ -> T.BChk.syn @@ R.Sub.elim @@ T.Var.syn tp)
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
