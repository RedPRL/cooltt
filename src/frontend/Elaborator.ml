open Core
open Basis
open Bwd

open CodeUnit

module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = RefineEnv
module Err = RefineError
module RM = RefineMonad
module R = Refiner
module T = Tactic
module Sem = Semantics

open Monad.Notation (RM)
module MU = Monad.Util (RM)

let rec unfold idents k =
  match idents with
  | [] -> k
  | ident :: idents ->
    let* res = RM.resolve ident in
    match res with
    | `Global sym ->
      let* env = RM.read in
      let veil = Veil.unfold [sym] @@ Env.get_veil env in
      RM.veil veil @@ unfold idents k
    | _ ->
      let* env = RM.read in
      let span = Env.location env in
      RM.throw @@ Err.RefineError (Err.UnboundVariable ident, span)

(* Account for the lambda-bound signature field dependencies.
    See [NOTE: Sig Code Quantifiers] for more info. *)
let bind_sig_tacs (tacs : ('a Ident.some * T.Chk.tac) list) : ('a Ident.some * T.Chk.tac) list =
  let bind_tac lbls (lbl, tac) =
    let tac = Bwd.fold_right (fun lbl tac -> R.Pi.intro ~ident:(lbl :> Ident.t) (fun _ -> tac)) lbls tac in
    Snoc (lbls, lbl) , (lbl, tac)
  in
  snd @@ ListUtil.map_accum_left bind_tac Emp tacs

module CoolTp :
sig
  include T.Tactic

  val as_tp : tac -> T.Tp.tac
  val pi : tac -> Ident.t -> tac -> tac
  val sg : tac -> Ident.t -> tac -> tac
  val signature : (Ident.user * tac) list -> tac
  val data : Ident.t -> (Ident.user * (Ident.t * tac) list) list -> tac
  val sub : tac -> T.Chk.tac -> T.Chk.tac -> tac
  val ext : int -> T.Chk.tac -> T.Chk.tac -> T.Chk.tac -> tac
  val nat : tac
  val circle : tac
  val univ : tac
  val dim : tac
  val cof : tac
  val prf : T.Chk.tac -> tac
  val locked_prf : T.Chk.tac -> tac
  val tp_var : Ident.t -> tac

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

  let as_codes =
    ListUtil.map_opt @@
    function
    | (_, Tp _) -> None
    | (lbl, Code tac) -> Some (lbl, tac)

  let as_tp_telescope (tacs : ('v Ident.some * tac) list) : ('v, T.Tp.tac) R.telescope =
    List.fold_right (fun (nm, tac) tele -> R.Bind (nm, as_tp tac, fun _ -> tele)) tacs R.Done

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

  let signature (tacs : (Ident.user * tac) list) : tac =
    match (as_codes tacs) with
    | Some tacs ->
      let tac = R.Univ.signature (bind_sig_tacs tacs) in
      Code tac
    | None ->
      let tele = as_tp_telescope tacs in
      let tac = R.Signature.formation tele in
      Tp tac

  let data (self : Ident.t) (tacs : (Ident.user * (Ident.t * tac) list) list) : tac =
    let ctors = fun _ -> List.map (CCPair.map_snd as_tp_telescope) tacs in
    Tp (R.Data.formation self ctors)

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
  let locked_prf tac = Tp (R.LockedPrf.formation tac)
  let tp_var i = Tp (R.Structural.lookup_tp_var i)
  let code tac = Code tac
end

let rec cool_chk_tp : CS.con -> CoolTp.tac =
  fun con ->
  CoolTp.update_span con.info @@
  match con.node with
  | CS.Pi ([], body) ->
    cool_chk_tp body
  | CS.Pi (CS.Cell cell :: cells, body) ->
    List.fold_right (CoolTp.pi (cool_chk_tp cell.tp)) cell.names @@
    cool_chk_tp {con with node = CS.Pi (cells, body)}
  | CS.Sg ([], body) ->
    cool_chk_tp body
  | CS.Sg (CS.Cell cell :: cells, body) ->
    List.fold_right (CoolTp.sg (cool_chk_tp cell.tp)) cell.names @@
    cool_chk_tp {con with node = CS.Sg (cells, body)}
  | CS.Signature cells ->
    let tacs = List.map (fun (CS.Field field) -> (field.lbl, cool_chk_tp field.tp)) cells in
    CoolTp.signature tacs
  | CS.Data {self; ctors} ->
    (* FIXME: This is bad. Think hard about identifiers *)
    (* FIXME: factor out the cell expansion logic *)
    let ctor (CS.Ctor {lbl; args}) = (lbl, List.concat_map (fun (CS.Cell {names; tp}) -> List.map (fun name -> (name, cool_chk_tp tp)) names) args) in
    CoolTp.data self (List.map ctor ctors)
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
  | CS.Locked cphi ->
    let tac_phi = chk_tm cphi in
    CoolTp.locked_prf tac_phi
  | CS.Var id ->
    CoolTp.tp_var id
  | _ -> CoolTp.code @@ chk_tm con


and chk_tp : CS.con -> T.Tp.tac =
  fun con ->
  T.Tp.update_span con.info @@
  CoolTp.as_tp @@ cool_chk_tp con

and chk_tp_in_tele (args : CS.cell list) (con : CS.con) : T.Tp.tac =
  let rec loop args =
    match args with
    | [] -> cool_chk_tp con
    | CS.Cell {names; tp} :: args ->
      CoolTp.update_span tp.info @@
      List.fold_right (CoolTp.pi (cool_chk_tp tp)) names @@
      loop args
  in
  CoolTp.as_tp @@ loop args

and chk_tm_in_tele (args : CS.cell list) (con : CS.con) : T.Chk.tac =
  let rec loop args =
    match args with
    | [] -> chk_tm con
    | CS.Cell {names; tp} :: args ->
      (* XXX a mechanical translation was done to support multiple names
         in a cell. Someone should rethink and refactor the code. *)
      List.fold_right
        (fun name body ->
           T.Chk.update_span tp.info @@
           Tactics.intro_implicit_connectives @@
           R.Pi.intro ~ident:name @@ fun _ -> body)
        names
        (loop args)
  in
  loop args

and chk_tm : CS.con -> T.Chk.tac =
  fun con ->
  T.Chk.update_span con.info @@
  Tactics.intro_subtypes @@
  match con.node with
  | CS.Hole (name, None) -> Refiner.Hole.unleash_hole name
  | CS.Hole (name, Some con) -> Refiner.Probe.probe_chk name @@ chk_tm con
  | CS.BoundaryHole None -> Refiner.Hole.unleash_hole None
  | CS.BoundaryHole (Some con) -> Refiner.Probe.probe_boundary (chk_tm con) (Refiner.Hole.silent_hole None)
  | CS.Unfold (idents, c) ->
    (* TODO: move to a trusted rule *)
    T.Chk.brule @@
    fun goal ->
    unfold idents @@ T.Chk.brun (chk_tm c) goal

  | CS.Generalize (ident, c) ->
    R.Structural.generalize ident (chk_tm c)

  | CS.Lam ([], body) ->
    chk_tm body

  | CS.Unlock (prf, bdy) ->
    R.LockedPrf.unlock (syn_tm prf) @@
    R.Pi.intro @@ fun _ -> chk_tm bdy

  | _ ->
    Tactics.intro_implicit_connectives @@
    match con.node with
    | CS.Underscore ->
      R.Prf.intro

    | CS.Lit n ->
      begin
        Tactics.match_goal @@ function
        | D.TpDim, _, _ -> RM.ret @@ R.Dim.literal n
        | _ -> RM.ret @@ R.Nat.literal n
      end

    | CS.Lam (nm :: names, body) ->
      R.Pi.intro ~ident:nm @@ fun _ ->
      chk_tm {con with node = CS.Lam (names, body)}

    | CS.LamElim cases ->
      Tactics.Elim.lam_elim @@ chk_cases cases

    | CS.Pair (c0, c1) ->
      begin
        Tactics.match_goal @@ function
        | D.Sg _, _, _ ->
          RM.ret @@ R.Sg.intro (chk_tm c0) (chk_tm c1)
        | D.ElUnstable (`V _), _, _ ->
          RM.ret @@ R.ElV.intro (chk_tm c0) (chk_tm c1)
        | D.ElUnstable (`HCom _), _, _ ->
          RM.ret @@ R.ElHCom.intro (chk_tm c0) (chk_tm c1)
        | tp, _, _ ->
          RM.expected_connective `Sg tp
      end

    | CS.Struct fields ->
      let tacs = List.map (fun (CS.Field field) -> (field.lbl, chk_tm field.tp)) fields in
      R.Signature.intro @@ R.Signature.find_field_tac tacs

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
      let tac (CS.Cell cell) = let tp = chk_tm cell.tp in List.map (fun name -> name, tp) cell.names in
      let tacs = cells |> List.concat_map tac in
      let quant base (nm, fam) = R.Univ.pi base (R.Pi.intro ~ident:nm fam) in
      Tactics.tac_nary_quantifier quant tacs @@ chk_tm body

    | CS.Sg (cells, body) ->
      let tac (CS.Cell cell) = let tp = chk_tm cell.tp in List.map (fun name -> name, tp) cell.names in
      let tacs = cells |> List.concat_map tac in
      let quant base (nm, fam) = R.Univ.sg base (R.Pi.intro ~ident:nm fam) in
      Tactics.tac_nary_quantifier quant tacs @@ chk_tm body

    | CS.Signature fields ->
      let tacs = bind_sig_tacs @@ List.map (fun (CS.Field field) -> field.lbl, chk_tm field.tp) fields in
      R.Univ.signature tacs

    | CS.Patch (tp, patches) ->
      let tacs = bind_sig_tacs @@ List.map (fun (CS.Field field) -> field.lbl, chk_tm field.tp) patches in
      R.Univ.patch (chk_tm tp) (R.Signature.find_field_tac tacs)

    | CS.Total (tp, patches) ->
      let tacs = bind_sig_tacs @@ List.map (fun (CS.Field field) -> field.lbl, chk_tm field.tp) patches in
      R.Univ.patch (R.Univ.total (syn_tm tp)) (R.Signature.find_field_tac tacs)

    | CS.Constructor {lbl; args} ->
      R.Data.intro lbl (List.map chk_tm args)

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
      let branch_tacs = splits |> List.map @@ fun (cphi, ctm) -> R.Cof.{cof = chk_tm cphi; bdy = fun _ -> chk_tm ctm} in
      R.Cof.split branch_tacs

    | CS.Ext (idents, tp, cases) ->
      let n = List.length idents in
      let tac_fam = chk_tm @@ CS.{node = CS.Lam (idents, tp); info = tp.info} in
      let tac_cof = chk_tm @@ CS.{node = CS.Lam (idents, {node = CS.Join (List.map fst cases); info = None}); info = None} in
      let tac_bdry = chk_tm @@ CS.{node = CS.Lam (idents @ [`Anon], {node = CS.CofSplit cases; info = None}); info = None} in
      R.Univ.ext n tac_fam tac_cof tac_bdry

    | _ ->
      Tactics.match_goal @@ fun (tp, _, _) ->
      match tp with
      | D.Pi _ ->
        let* env = RM.read in
        let lvl = RefineEnv.size env in
        RM.ret @@ R.Pi.intro @@ fun _ -> chk_tm @@ CS.{node = CS.Ap (con, [CS.{node = DeBruijnLevel lvl; info = None}]); info = None}
      | D.Sg _ ->
        RM.ret @@ R.Sg.intro (chk_tm @@ CS.{node = CS.Fst con; info = None}) (chk_tm @@ CS.{node = CS.Snd con; info = None})
      | D.Signature _ ->
        let field_tac lbl = Option.some @@ chk_tm @@ CS.{node = CS.Proj (con, lbl); info = None} in
        RM.ret @@ R.Signature.intro field_tac
      | _ ->
        RM.ret @@ T.Chk.syn @@ syn_tm con

and syn_tm : CS.con -> T.Syn.tac =
  function con ->
    T.Syn.update_span con.info @@
    Tactics.elim_implicit_connectives @@
    match con.node with
    | CS.Hole (name, None) -> Refiner.Hole.unleash_syn_hole name
    | CS.Hole (name, Some con) -> Refiner.Probe.probe_syn name @@ syn_tm con
    | CS.BoundaryHole None ->  Refiner.Hole.unleash_syn_hole None
    | CS.BoundaryHole (Some con) ->  Refiner.Probe.probe_syn None @@ syn_tm con
    | CS.Var id ->
      R.Structural.lookup_var id
    | CS.DeBruijnLevel lvl ->
      R.Structural.level lvl
    | CS.Ap (t, []) ->
      syn_tm t
    | CS.Ap (t, ts) ->
      let rec go acc ts =
        match ts with
        | [] -> Tactics.elim_implicit_connectives acc
        | t :: ts ->
          let tac = R.Pi.apply (Tactics.elim_implicit_connectives acc) t in
          go tac ts
      in
      go (syn_tm t) @@ List.map chk_tm ts
    | CS.Fst t ->
      R.Sg.pi1 @@ syn_tm t
    | CS.Snd t ->
      R.Sg.pi2 @@ syn_tm t
    | CS.Proj (t, ident) ->
      R.Signature.proj (syn_tm t) ident
    | CS.VProj t ->
      R.ElV.elim @@ syn_tm t
    | CS.Cap t ->
      R.ElHCom.elim @@ syn_tm t
    | CS.Elim {mot; cases; scrut} ->
      Tactics.Elim.elim
        (chk_tm mot)
        (chk_cases cases)
        (syn_tm scrut)
    | CS.Rec {mot; cases; scrut} ->
      let mot_tac = chk_tm mot in
      R.Structural.let_syn (T.Syn.ann mot_tac R.Univ.formation) @@ fun tp ->
      Tactics.Elim.elim
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
        Tactics.intro_implicit_connectives @@
        T.Chk.syn @@
        Tactics.elim_implicit_connectives @@
        R.Univ.hcom code_tac (chk_tm src) (T.Chk.syn @@ T.Var.syn i) (chk_tm cof) (chk_tm tm)
      in
      T.Syn.ann tac @@
      R.Pi.formation R.Dim.formation (`Anon, fun _ -> R.El.formation code_tac)
    | CS.Com (fam, src, trg, cof, tm) ->
      R.Univ.com (chk_tm fam) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
    | _ ->
      T.Syn.rule @@
      RM.throw @@ ElabError.ElabError (ElabError.ExpectedSynthesizableTerm con.node, con.info)

and chk_cases cases =
  List.map chk_case cases

and chk_case (pat, c) =
  pat, chk_tm c

let rec modifier_ (con : CS.con) =
  let open Yuujinchou.Pattern in
  RM.update_span con.info @@
  match con.node with
  | CS.ModAny -> RM.ret any
  | CS.ModOnly path -> RM.ret @@ only_subtree path
  | CS.ModRename (path1, path2) -> RM.ret @@ renaming_subtree path1 path2
  | CS.ModNone -> RM.ret none
  | CS.ModExcept path -> RM.ret @@ except_subtree path
  | CS.ModSeq l -> seq <@> MU.map modifier_ l
  | CS.ModUnion l -> union <@> MU.map modifier_ l
  | CS.ModInSubtree (p, m) -> in_subtree p <@> modifier_ m
  | CS.ModPrint lbl -> RM.ret @@ hook @@ `Print lbl
  | _ -> RM.throw @@ ElabError.ElabError (ElabError.ExpectedSynthesizableTerm con.node, con.info)

let modifier con =
  Option.fold ~none:(RM.ret Yuujinchou.Pattern.any) ~some:modifier_ con
