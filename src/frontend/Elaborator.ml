open Core
open Basis

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

let do_rename rn nm =
  List.assoc_opt nm (rn :> (Ident.t * Ident.t) list)

module CoolTp :
sig
  include T.Tactic
  type tele_tac

  val as_tp : tac -> T.Tp.tac
  val as_tele : tele_tac -> T.Tele.tac

  val pi : tac -> Ident.t -> tac -> tac
  val sg : tac -> Ident.t -> tac -> tac
  val signature : tele_tac -> tac
  val sub : tac -> T.Chk.tac -> T.Chk.tac -> tac
  val ext : int -> T.Chk.tac -> T.Chk.tac -> T.Chk.tac -> tac
  val nat : tac
  val circle : tac
  val univ : tac
  val dim : tac
  val cof : tac
  val prf : T.Chk.tac -> tac
  val code : T.Chk.tac -> tac

  val empty : tele_tac
  val cell : Ident.t -> tac -> tele_tac -> tele_tac
  val include_ : (Ident.t -> Ident.t option) -> tele_tac -> tele_tac -> tele_tac
  val tele_of_sign : tac -> tele_tac
end =
struct
  type tac =
    | Tp of T.Tp.tac
    | Code of T.Chk.tac

  type tele_tac =
    | Tele of T.Tele.tac
    | KanTele of T.KanTele.tac

  let whnf =
    function
    | Tp tac -> Tp (T.Tp.whnf tac)
    | Code tac -> Code (T.Chk.whnf tac)

  let update_span span =
    function
    | Tp tac -> Tp (T.Tp.update_span span tac)
    | Code tac -> Code (T.Chk.update_span span tac)

  let as_tp =
    function
    | Tp tac -> tac
    | Code tac -> R.El.formation tac

  let as_tele =
    function
    | Tele tac -> tac
    | KanTele tac -> R.Telescope.el tac

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

  let signature (tac : tele_tac) : tac =
    match tac with
    | KanTele tac ->
      let tac = R.Univ.signature tac in
      Code tac
    | Tele tac ->
      let tac = R.Signature.formation tac in
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

  let empty = KanTele R.KanTelescope.empty

  let cell ident tac tele_tac =
    match tac, tele_tac with
    | Code tac, KanTele tele_tac ->
      KanTele (R.KanTelescope.cell tac (ident, fun _ -> tele_tac))
    | _, _ ->
      let tac = as_tp tac in
      let tele_tac = as_tele tele_tac in
      Tele (R.Telescope.cell tac (ident, fun _ -> tele_tac))

  let include_ rename inc_tac tele_tac =
    match inc_tac, tele_tac with
    | KanTele inc_tac, KanTele tele_tac ->
      KanTele (R.KanTelescope.include_ rename inc_tac (fun _ -> tele_tac))
    | _, _ ->
      let inc_tac = as_tele inc_tac in
      let tele_tac = as_tele tele_tac in
      Tele (R.Telescope.include_ rename inc_tac (fun _ -> tele_tac))

  let tele_of_sign tac =
    match tac with
    | Code tac ->
      KanTele (Tactics.kan_tele_of_sign tac)
    | Tp tac ->
      Tele (Tactics.tele_of_sign tac)
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
    let tac = cool_chk_tele cells in
    CoolTp.signature tac
  | CS.Dim -> CoolTp.dim
  | CS.Cof -> CoolTp.cof
  | CS.Prf phi -> CoolTp.prf @@ chk_tm phi
  | CS.Sub (ctp, cphi, ctm) -> CoolTp.sub (cool_chk_tp ctp) (chk_tm cphi) (chk_tm ctm)
  | CS.Ext (idents, tp, cases) ->
    let n = List.length idents in
    let tac_fam = chk_tm @@ CS.{node = CS.Lam (idents, tp); info = tp.info} in
    let tac_cof = chk_tm @@ CS.{node = CS.Lam (idents, {node = CS.Join (List.map fst cases); info = None}); info = None} in
    let tac_bdry = chk_tm @@ CS.{node = CS.Lam (idents, {node = CS.CofSplit cases; info = None}); info = None} in
    CoolTp.ext n tac_fam tac_cof tac_bdry
  | _ -> CoolTp.code @@ chk_tm con

and cool_chk_tele : CS.field list -> CoolTp.tele_tac =
  function
  | [] ->
    CoolTp.empty
  | `Field (lbl, con) :: fields ->
    CoolTp.cell (lbl :> Ident.t) (cool_chk_tp con) (cool_chk_tele fields)
  | `Include (con, rn) :: fields ->
    CoolTp.include_ (do_rename rn) (CoolTp.tele_of_sign @@ cool_chk_tp con) (cool_chk_tele fields)

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
  match con.node with
  | CS.Generalize (ident, c) ->
    R.Structural.generalize ident (chk_tm c)

  | CS.Visualize -> R.Probe.probe_goal_chk (fun ctx goal -> RM.ret @@ Server.dispatch_goal ctx goal) @@ R.Hole.unleash_hole None

  | CS.HComChk (src, trg, tm) ->
    R.Univ.hcom_chk (chk_tm src) (chk_tm trg) (chk_tm tm)

  | CS.HFillChk (src, tm) ->
    R.Pi.intro ~ident:(Ident.machine "i") @@ fun i ->
    R.Univ.hcom_chk (chk_tm src) (T.Chk.syn @@ T.Var.syn i) (chk_tm tm)

  | CS.Lam ([], body) ->
    chk_tm body

  | CS.Let (c, ident, body) ->
    R.Structural.let_ ~ident (syn_tm c) @@ fun _ -> chk_tm body

  | _ ->
    Tactics.intro_subtypes_and_total @@
    match con.node with
    | CS.Hole ({name; silent=false}, None) -> Refiner.Hole.unleash_hole name
    | CS.Hole ({name; silent=false}, Some con) -> Refiner.Probe.probe_chk name @@ chk_tm con
    | CS.Hole ({name; silent=true}, None) -> Refiner.Hole.silent_hole name
    | CS.Hole ({name=_; silent=true}, Some con) -> chk_tm con
    | CS.BoundaryHole None -> Refiner.Hole.unleash_hole None
    | CS.BoundaryHole (Some con) -> Refiner.Probe.probe_boundary (chk_tm con) (Refiner.Hole.silent_hole None)

    | CS.Generalize (ident, c) ->
      R.Structural.generalize ident (chk_tm c)

    | CS.Unfold (idents, c) ->
      R.Structural.unfold idents (chk_tm c)

    | CS.Abstract (name, c) ->
      R.Structural.abstract ~name (chk_tm c)

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

      | CS.Open (tm,rn,body) ->
        Tactics.open_ (syn_tm tm) (do_rename rn) @@ fun _ -> chk_tm body

      | CS.Struct fields ->
        let tacs =
          fields |> List.map @@
          function
          | `Field (lbl, con) -> `Field ((lbl :> Ident.t), chk_tm con)
          | `Include (con, rn) -> `Include (syn_tm con, do_rename rn)
        in
        R.Signature.intro tacs

      | CS.Suc c ->
        R.Nat.suc (chk_tm c)

      | CS.Base ->
        R.Circle.base

      | CS.Loop c ->
        R.Circle.loop (chk_tm c)

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
        let tac = chk_kan_tele fields in
        R.Univ.signature tac
      (* let tacs = *)
      (*   fields |> List.map @@ function *)
      (*   | `Field (lbl, con) -> `Field ((lbl :> Ident.t), chk_tm con) *)
      (*   | `Include (inc, rn) -> `Include (chk_tm inc, do_rename rn) *)
      (* in *)
      (* R.Univ.signature tacs *)

      | CS.Patch (tp, patches) ->
        let tacs =
          patches |> List.map @@ function
          | `Patch (lbl, con) ->
            (lbl :> Ident.t), `Patch (chk_tm con)
          | `Subst (lbl, con) ->
            (lbl :> Ident.t), `Subst (chk_tm con)
        in
        R.Univ.patch (chk_tm tp) (fun nm -> List.assoc_opt nm tacs)

      | CS.V (r, pcode, code, pequiv) ->
        R.Univ.code_v (chk_tm r) (chk_tm pcode) (chk_tm code) (chk_tm pequiv)

      | CS.CofEq (c0, c1) ->
        R.Cof.eq (chk_tm c0) (chk_tm c1)

      | CS.CofLe (c0, c1) ->
        R.Cof.le (chk_tm c0) (chk_tm c1)

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
        let tac_bdry = chk_tm @@ CS.{node = CS.Lam (idents, {node = CS.CofSplit cases; info = None}); info = None} in
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

        | D.Signature tele ->
          let lbls = D.tele_lbls tele in
          let tacs =
            lbls |> List.map @@
            function
            | lbl -> `Field (lbl, chk_tm @@ CS.{ node = CS.Proj (con, lbl); info = None })
          in
          (* let fields = List.map (fun lbl -> `Field (lbl,chk_tm @@ CS.{node = CS.Proj (con, lbl); info = None})) lbls in *)
          RM.ret @@ R.Signature.intro tacs
        | _ ->
          RM.ret @@ Tactics.intro_conversions @@ syn_tm con

and syn_tm : ?elim_total:bool -> CS.con -> T.Syn.tac =
  fun ?(elim_total = true) con ->
  T.Syn.update_span con.info @@
  (if elim_total then Tactics.elim_implicit_connectives_and_total else Tactics.elim_implicit_connectives) @@
  match con.node with
  | CS.Hole ({name; silent=false}, None) -> Refiner.Hole.unleash_syn_hole name
  | CS.Hole ({name; silent=false}, Some con) -> Refiner.Probe.probe_syn name @@ syn_tm con
  | CS.Hole ({name; silent=true}, None) -> Refiner.Hole.silent_syn_hole name
  | CS.Hole ({name=_; silent=true}, Some con) -> syn_tm con
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
    R.Signature.proj (syn_tm ~elim_total:false t) ident
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

  | CS.Open (tm,rn,bdy) -> Tactics.open_syn (syn_tm tm) (do_rename rn) @@ fun _ -> syn_tm bdy
  | CS.Ann {term; tp} ->
    T.Syn.ann (chk_tm term) (chk_tp tp)
  | CS.Coe (tp, src, trg, body) ->
    R.Univ.coe (chk_tm tp) (chk_tm src) (chk_tm trg) (chk_tm body)
  | CS.HCom (tp, src, trg, cof, tm) ->
    R.Univ.hcom (chk_tm tp) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
  | CS.HFill (code, src, cof, tm) ->
    let code_tac = chk_tm code in
    let tac =
      R.Pi.intro ~ident:(Ident.machine "i") @@ fun i ->
      Tactics.intro_implicit_connectives @@
      T.Chk.syn @@
      Tactics.elim_implicit_connectives @@
      R.Univ.hcom code_tac (chk_tm src) (T.Chk.syn @@ T.Var.syn i) (chk_tm cof) (chk_tm tm)
    in
    T.Syn.ann tac @@
    R.Pi.formation R.Dim.formation (Ident.anon, fun _ -> R.El.formation code_tac)
  | CS.Com (fam, src, trg, cof, tm) ->
    R.Univ.com (chk_tm fam) (chk_tm src) (chk_tm trg) (chk_tm cof) (chk_tm tm)
  | CS.Equations {code; eqns} ->
    let open Tactics.Equations in
    let code_tac = chk_tm code in
    let rec mk_steps : CS.eqns CS.step -> T.Syn.tac * T.Chk.tac * T.Chk.tac =
      function
      | Equals (lhs, p, eqns) ->
        let q_tac, mid_tac, rhs_tac = mk_eqns eqns in
        let lhs_tac = chk_tm lhs in
        step code_tac lhs_tac mid_tac rhs_tac (chk_tm p) (T.Chk.syn q_tac), lhs_tac, rhs_tac
      | Trivial (lhs, eqns) ->
        let q_tac, mid_tac, rhs_tac = mk_eqns eqns in
        let lhs_tac = chk_tm lhs in
        step code_tac lhs_tac mid_tac rhs_tac (T.Chk.syn @@ qed code_tac lhs_tac) (T.Chk.syn q_tac), lhs_tac, rhs_tac
    and mk_eqns : CS.eqns -> T.Syn.tac * T.Chk.tac * T.Chk.tac =
      function
      | Step s ->
        mk_steps s
      | Qed x ->
        let x_tac = chk_tm x in
        qed code_tac x_tac, x_tac, x_tac
    in
    let (tac, _, _ ) = mk_steps eqns in
    tac
  | _ ->
    T.Syn.rule @@
    RM.throw @@ ElabError.ElabError (ElabError.ExpectedSynthesizableTerm con.node, con.info)

and chk_kan_tele fields =
  let chk_field field tele_tac =
    match field with
    | `Field (lbl, con) ->
      R.KanTelescope.cell (chk_tm con) ((lbl :> Ident.t), fun _ -> tele_tac)
    | `Include (con, rn) ->
      R.KanTelescope.include_ (do_rename rn) (Tactics.kan_tele_of_sign @@ chk_tm con) (fun _ -> tele_tac)
  in
  List.fold_right chk_field fields R.KanTelescope.empty

and chk_cases cases =
  List.map chk_case cases

and chk_case (pat, c) =
  pat, chk_tm c

let rec modifier (con : CS.con) =
  let open Yuujinchou.Language in
  RM.update_span con.info @@
  match con.node with
  | CS.ModAll -> RM.ret all
  | CS.ModOnly path -> RM.ret @@ only path
  | CS.ModRename (path1, path2) -> RM.ret @@ renaming path1 path2
  | CS.ModNone -> RM.ret none
  | CS.ModExcept path -> RM.ret @@ except path
  | CS.ModSeq l -> seq <@> MU.map modifier l
  | CS.ModUnion l -> union <@> MU.map modifier l
  | CS.ModInSubtree (p, m) -> in_ p <@> modifier m
  | CS.ModPrint {name; silent=false} -> RM.ret @@ hook @@ `Print name
  | CS.ModPrint {name=_; silent=true} -> RM.ret @@ seq []
  | _ -> RM.throw @@ ElabError.ElabError (ElabError.ExpectedSynthesizableTerm con.node, con.info)
