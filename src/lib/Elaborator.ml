module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module R = Refiner
module T = Tactic
module Sem = Semantics

open Basis
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
      let* env = EM.read in
      let span = Env.location env in
      EM.throw @@ Err.ElabError (Err.UnboundVariable ident, span)

module CoolTp :
sig
  include T.Tactic

  val as_tp : tac -> T.Tp.tac
  val pi : tac -> Ident.t -> tac -> tac
  val sg : tac -> Ident.t -> tac -> tac
  val sub : tac -> T.Chk.tac -> T.Chk.tac -> tac
  val ext : int -> T.Chk.tac -> T.Chk.tac -> T.Chk.tac -> tac
  val nat : tac
  val circle : tac
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

  let whnf ~style =
    function
    | Tp tac -> Tp (T.Tp.whnf ~style tac)
    | Code tac -> Code (T.Chk.whnf ~style tac)

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
      let tac = R.Univ.pi tac_base @@ R.Pi.intro ~ident @@ fun _ -> tac_fam in
      Code tac
    | _ ->
      let tac_base = as_tp tac_base in
      let tac_fam = as_tp tac_fam in
      let tac = R.Pi.formation tac_base (ident, fun _ -> tac_fam) in
      Tp tac

  let sg (tac_base : tac) (ident : Ident.t) (tac_fam : tac) : tac =
    match tac_base, tac_fam with
    | Code tac_base, Code tac_fam ->
      let tac = R.Univ.sg tac_base @@ R.Pi.intro ~ident @@ fun _ -> tac_fam in
      Code tac
    | _ ->
      let tac_base = as_tp tac_base in
      let tac_fam = as_tp tac_fam in
      let tac = R.Sg.formation tac_base (ident, fun _ -> tac_fam) in
      Tp tac

  let sub tac_tp tac_phi tac_pel : tac =
    let tac = R.Sub.formation (as_tp tac_tp) tac_phi (fun _ -> tac_pel) in
    Tp tac

  let ext n tac_tp tac_cof tac_bdry =
    let tac = R.Univ.ext n tac_tp tac_cof tac_bdry in
    Code tac

  let nat = Code R.Univ.nat
  let circle = Code R.Univ.circle
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
  | CS.Ext (idents, tp, cases) ->
    let n = List.length idents in
    let tac_fam = chk_tm @@ CS.{node = CS.Lam (idents, tp); info = tp.info} in
    let tac_cof = chk_tm @@ CS.{node = CS.Lam (idents, {node = CS.Join (List.map fst cases); info = None}); info = None} in
    let tac_bdry = chk_tm @@ CS.{node = CS.Lam (idents @ [`Anon], {node = CS.CofSplit cases; info = None}); info = None} in
    CoolTp.ext n tac_fam tac_cof tac_bdry
  | _ -> CoolTp.code @@ chk_tm con


and chk_tp : CS.con -> T.Tp.tac =
  fun con ->
  T.Tp.update_span con.info @@
  CoolTp.as_tp @@ cool_chk_tp con

and chk_tp_in_tele (args : CS.cell list) (con : CS.con) : T.Tp.tac =
  let rec loop args =
    match args with
    | [] -> cool_chk_tp con
    | CS.Cell {name; tp} :: args ->
      CoolTp.update_span tp.info @@
      CoolTp.pi (cool_chk_tp tp) name @@
      loop args
  in
  CoolTp.as_tp @@ loop args

and chk_tm_in_tele (args : CS.cell list) (con : CS.con) : T.Chk.tac =
  let rec loop args =
    match args with
    | [] -> chk_tm con
    | CS.Cell {name; tp} :: args ->
      T.Chk.update_span tp.info @@
      R.Tactic.intro_implicit_connectives @@
      R.Pi.intro ~ident:name @@ fun _ ->
      loop args
  in
  loop args

and chk_tm : CS.con -> T.Chk.tac =
  fun con ->
  T.Chk.update_span con.info @@
  R.Tactic.intro_subtypes @@
  match con.node with
  | CS.Hole name ->
    R.Hole.unleash_hole name `Rigid

  | CS.Unfold (idents, c) ->
    (* TODO: move to a trusted rule *)
    T.Chk.brule @@
    fun goal ->
      unfold idents @@ T.Chk.brun (chk_tm c) goal

  | CS.Generalize (ident, c) ->
    R.Structural.generalize ident (chk_tm c)

  | CS.Lam ([], body) ->
    chk_tm body

  | _ ->
    R.Tactic.intro_implicit_connectives @@
    match con.node with
    | CS.Underscore ->
      R.Prf.intro

    | CS.Lit n ->
      begin
        R.Tactic.match_goal @@ function
        | D.TpDim, _, _ -> EM.ret @@ R.Dim.literal n
        | _ -> EM.ret @@ R.Nat.literal n
      end

    | CS.Lam (nm :: names, body) ->
      R.Pi.intro ~ident:nm @@ fun _ ->
      chk_tm {con with node = CS.Lam (names, body)}

    | CS.LamElim cases ->
      R.Tactic.Elim.lam_elim @@ chk_cases cases

    | CS.Pair (c0, c1) ->
      begin
        R.Tactic.match_goal @@ function
        | D.Sg _, _, _ ->
          EM.ret @@ R.Sg.intro (chk_tm c0) (chk_tm c1)
        | D.ElUnstable (`V _), _, _ ->
          EM.ret @@ R.ElV.intro (chk_tm c0) (chk_tm c1)
        | D.ElUnstable (`HCom _), _, _ ->
          EM.ret @@ R.ElHCom.intro (chk_tm c0) (chk_tm c1)
        | tp, _, _ ->
          EM.expected_connective `Sg tp
      end

    | CS.Suc c ->
      R.Nat.suc (chk_tm c)

    | CS.Base ->
      R.Circle.base

    | CS.Loop c ->
      R.Circle.loop (chk_tm c)

    | CS.Let (c, ident, body) ->
      R.Structural.let_ ~ident (syn_tm c) @@ fun _ -> chk_tm body

    | CS.Nat ->
      R.Univ.nat

    | CS.Circle ->
      R.Univ.circle

    | CS.Type ->
      R.Univ.univ

    | CS.Pi (cells, body) ->
      let tac (CS.Cell cell) = cell.name, chk_tm cell.tp in
      let tacs = cells |> List.map tac in
      let quant base (nm, fam) = R.Univ.pi base (R.Pi.intro ~ident:nm fam) in
      R.Tactic.tac_nary_quantifier quant tacs @@ chk_tm body

    | CS.Sg (cells, body) ->
      let tacs = cells |> List.map @@ fun (CS.Cell cell) -> cell.name, chk_tm cell.tp in
      let quant base (nm, fam) = R.Univ.sg base (R.Pi.intro ~ident:nm fam) in
      R.Tactic.tac_nary_quantifier quant tacs @@ chk_tm body

    | CS.V (r, pcode, code, pequiv) ->
      R.Univ.code_v (chk_tm r) (chk_tm pcode) (chk_tm code) (chk_tm pequiv)

    | CS.CofEq (c0, c1) ->
      R.Cof.eq (chk_tm c0) (chk_tm c1)

    | CS.Join cs ->
      R.Cof.join (List.map chk_tm cs)

    | CS.BotC ->
      R.Cof.join []

    | CS.Meet cs ->
      R.Cof.meet (List.map chk_tm cs)

    | CS.TopC ->
      R.Cof.meet []

    | CS.CofBoundary c ->
      R.Cof.boundary (chk_tm c)

    | CS.CofSplit splits ->
      let branch_tacs = splits |> List.map @@ fun (cphi, ctm) -> chk_tm cphi, fun _ -> chk_tm ctm in
      R.Cof.split branch_tacs

    | CS.Ext (idents, tp, cases) ->
      let n = List.length idents in
      let tac_fam = chk_tm @@ CS.{node = CS.Lam (idents, tp); info = tp.info} in
      let tac_cof = chk_tm @@ CS.{node = CS.Lam (idents, {node = CS.Join (List.map fst cases); info = None}); info = None} in
      let tac_bdry = chk_tm @@ CS.{node = CS.Lam (idents @ [`Anon], {node = CS.CofSplit cases; info = None}); info = None} in
      R.Univ.ext n tac_fam tac_cof tac_bdry

    | _ ->
      R.Tactic.match_goal @@ fun (tp, _, _) ->
      match tp with
      | D.Pi _ ->
        let* env = EM.read in
        let lvl = ElabEnv.size env in
        EM.ret @@ R.Pi.intro @@ fun _ -> chk_tm @@ CS.{node = CS.Ap (con, [CS.{node = DeBruijnLevel lvl; info = None}]); info = None}
      | D.Sg _ ->
        EM.ret @@ R.Sg.intro (chk_tm @@ CS.{node = CS.Fst con; info = None}) (chk_tm @@ CS.{node = CS.Snd con; info = None})
      | _ ->
        EM.ret @@ T.Chk.syn @@ syn_tm con

and syn_tm : CS.con -> T.Syn.tac =
  function con ->
    T.Syn.update_span con.info @@
    R.Tactic.elim_implicit_connectives @@
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
        | [] -> R.Tactic.elim_implicit_connectives acc
        | t :: ts ->
          let tac = R.Pi.apply (R.Tactic.elim_implicit_connectives acc) t in
          go tac ts
      in
      go (syn_tm t) @@ List.map chk_tm ts
    | CS.Fst t ->
      R.Sg.pi1 @@ syn_tm t
    | CS.Snd t ->
      R.Sg.pi2 @@ syn_tm t
    | CS.VProj t ->
      R.ElV.elim @@ syn_tm t
    | CS.Cap t ->
      R.ElHCom.elim @@ syn_tm t
    | CS.Elim {mot; cases; scrut} ->
      R.Tactic.Elim.elim
        (chk_tm mot)
        (chk_cases cases)
        (syn_tm scrut)
    | CS.Rec {mot; cases; scrut} ->
      let mot_tac = chk_tm mot in
      R.Structural.let_syn (T.Syn.ann mot_tac R.Univ.formation) @@ fun tp ->
      R.Tactic.Elim.elim
        (R.Pi.intro @@ fun _ -> T.Chk.syn @@ R.Sub.elim @@ T.Var.syn tp)
        (chk_cases cases)
        (syn_tm scrut)

    | CS.Ann {term; tp} ->
      T.Syn.ann (chk_tm term) (chk_tp tp)
    | CS.Unfold (idents, c) ->
      (* TODO: move to a primitive rule *)
      T.Syn.rule @@ unfold idents @@ T.Syn.run @@ syn_tm c
    | CS.Coe (tp, src, trg, body) ->
      R.Univ.coe (chk_tm tp) (chk_tm src) (chk_tm trg) (chk_tm body)
    | CS.HCom (tp, src, trg, cof, tm) ->
      R.Univ.hcom (chk_tm tp) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
    | CS.HFill (code, src, cof, tm) ->
      let code_tac = chk_tm code in
      let tac =
        R.Pi.intro ~ident:(`Machine "i") @@ fun i ->
        R.Tactic.intro_implicit_connectives @@
        T.Chk.syn @@
        R.Tactic.elim_implicit_connectives @@
        R.Univ.hcom code_tac (chk_tm src) (T.Chk.syn @@ T.Var.syn i) (chk_tm cof) (chk_tm tm)
      in
      T.Syn.ann tac @@
      R.Pi.formation R.Dim.formation (`Anon, fun _ -> R.El.formation code_tac)
    | CS.Com (fam, src, trg, cof, tm) ->
      R.Univ.com (chk_tm fam) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
    | _ ->
      T.Syn.rule @@
      EM.throw @@ Err.ElabError (Err.ExpectedSynthesizableTerm con.node, con.info)

and chk_cases cases =
  List.map chk_case cases

and chk_case (pat, c) =
  pat, chk_tm c
