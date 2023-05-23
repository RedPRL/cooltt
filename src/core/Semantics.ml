open Basis
open Bwd
open Bwd.Infix

open CodeUnit

module S = Syntax
module D = Domain

exception Todo
exception CJHM
exception CFHM
exception CCHM

exception NbeFailed of string

module Splice = Splice
module TB = TermBuilder

module CM = struct include Monads.CmpM include Monad.Notation (Monads.CmpM) module MU = Monad.Util (Monads.CmpM) end
module EvM = struct include Monads.EvM include Monad.Notation (Monads.EvM) module MU = Monad.Util (Monads.EvM) end

type 'a whnf = [`Done | `Reduce of 'a]


let cut_frm ~tp ~cut frm =
  D.Cut {tp; cut = D.push frm cut}


let get_local i =
  let open EvM in
  let* env = EvM.read_local in
  match BwdLabels.nth env.conenv i with
  | v -> EvM.ret v
  | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

let get_local_tp i =
  let open EvM in
  let* env = EvM.read_local in
  match BwdLabels.nth env.tpenv i with
  | v -> EvM.ret v
  | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

let rec cof_con_to_cof : (D.con, D.con) Kado.Syntax.endo -> D.cof CM.m =
  let open CM in
  let module K = Kado.Syntax in
  function
  | K.Le (r, s) ->
    let+ r = con_to_dim r
    and+ s = con_to_dim s in
    CofBuilder.le r s
  | K.Join phis ->
    let+ phis = MU.map con_to_cof phis in
    CofBuilder.join phis
  | K.Meet phis ->
    let+ phis = MU.map con_to_cof phis in
    CofBuilder.meet phis

and con_to_cof =
  let open CM in
  fun con ->
    whnf_inspect_con con |>>
    function
    | D.Cof cof -> cof_con_to_cof cof
    | D.Cut {cut = D.Var l, []; _} -> ret @@ CofBuilder.var (CofVar.Local l)
    | D.Cut {cut = D.Global sym, []; _} -> ret @@ CofBuilder.var (CofVar.Axiom sym)
    | _ -> throw @@ NbeFailed "con_to_cof"

and con_to_dim =
  let open CM in
  fun con ->
    whnf_inspect_con con |>>
    function
    | D.Dim0 -> ret Dim.Dim0
    | D.Dim1 -> ret Dim.Dim1
    | D.DimProbe x -> ret @@ Dim.DimProbe x
    | D.Cut {cut = D.Var l, []; _} -> ret @@ Dim.DimVar (CofVar.Local l)
    | D.Cut {cut = D.Global sym, []; _} -> ret @@ Dim.DimVar (CofVar.Axiom sym)
    | con ->
      Format.eprintf "bad: %a@." D.pp_con con;
      throw @@ NbeFailed "con_to_dim"

and subst_con : D.dim -> DimProbe.t -> D.con -> D.con CM.m =
  fun r x con ->
  CM.ret @@ D.LetSym (r, x, con)

and push_subst_con : D.dim -> DimProbe.t -> D.con -> D.con CM.m =
  fun r x ->
  let open CM in
  let module K = Kado.Syntax in
  function
  | D.Dim0 | D.Dim1 | D.Prf | D.Zero | D.Base | D.StableCode (`Nat | `Circle | `Univ) as con -> ret con
  | D.LetSym (s, y, con) ->
    push_subst_con r x @<< push_subst_con s y con
  | D.Suc con ->
    let+ con = subst_con r x con in
    D.Suc con
  | D.Loop s ->
    let+ s = subst_dim r x s in
    D.Loop s
  | D.Lam (ident, clo) ->
    let+ clo = subst_clo r x clo in
    D.Lam (ident, clo)
  | BindSym (y, con) ->
    begin
      test_sequent [] (CofBuilder.eq (Dim.DimProbe x) (Dim.DimProbe y)) |>>
      function
      | true ->
        ret @@ D.BindSym (y, con)
      | false ->
        let+ con = subst_con r x con in
        D.BindSym (y, con)
    end
  | D.Pair (con0, con1) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1 in
    D.Pair (con0, con1)
  | D.Struct fields ->
    let+ fields = subst_fields r x fields in
    D.Struct fields
  | D.StableCode code ->
    let+ code = subst_stable_code r x code in
    D.StableCode code
  | D.ElIn con ->
    let+ con = subst_con r x con in
    D.ElIn con
  | D.SubIn con ->
    let+ con = subst_con r x con in
    D.SubIn con
  | D.Cof (K.Join phis) ->
    let+ phis = MU.map (subst_con r x) phis in
    D.Cof (K.Join phis)
  | D.Cof (K.Meet phis) ->
    let+ phis = MU.map (subst_con r x) phis in
    D.Cof (K.Meet phis)
  | D.Cof (K.Le (s, s')) ->
    let+ s = subst_con r x s
    and+ s' = subst_con r x s' in
    D.Cof (K.Le (s, s'))
  | D.FHCom (tag, s, s', phi, bdy) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ bdy = subst_con r x bdy in
    D.FHCom (tag, s, s', phi, bdy)
  | D.Box (s, s', phi, sides, cap) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ sides = subst_con r x sides
    and+ cap = subst_con r x cap in
    D.Box (s, s', phi, sides, cap)
  | D.UnstableCode (`V (s, pcode, code, pequiv)) ->
    let+ s = subst_dim r x s
    and+ pcode = subst_con r x pcode
    and+ code = subst_con r x code
    and+ pequiv = subst_con r x pequiv in
    D.UnstableCode (`V (s, pcode, code, pequiv))
  | D.UnstableCode (`HCom (s, s', phi, bdy)) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ bdy = subst_con r x bdy in
    D.UnstableCode (`HCom (s, s', phi, bdy))
  | D.VIn (s, equiv, pivot, base) ->
    let+ s = subst_dim r x s
    and+ equiv = subst_con r x equiv
    and+ pivot = subst_con r x pivot
    and+ base = subst_con r x base in
    D.VIn (s, equiv, pivot, base)
  | D.DimProbe y as con ->
    begin
      test_sequent [] (CofBuilder.eq (Dim.DimProbe x) (Dim.DimProbe y)) |>>
      function
      | true ->
        ret @@ D.dim_to_con r
      | false ->
        ret con
    end
  | D.Cut {tp; cut} ->
    let+ tp = subst_tp r x tp
    and+ cut = subst_cut r x cut in
    D.Cut {tp; cut}
  | D.Split branches ->
    let go_branch (phi, clo) =
      let+ phi = subst_cof r x phi
      and+ clo = subst_clo r x clo in
      (phi, clo)
    in
    let+ branches = MU.map go_branch branches in
    D.Split branches

and subst_fields : D.dim -> DimProbe.t -> D.fields -> D.fields CM.m =
  let open CM in
  fun r x ->
    function
    | D.Fields fields ->
      let+ fields = MU.map (MU.second (subst_con r x)) fields
      in D.Fields fields

and subst_dim : D.dim -> DimProbe.t -> D.dim -> D.dim CM.m =
  fun r x s ->
  let open CM in
  con_to_dim @<< push_subst_con r x @@ D.dim_to_con s

and subst_cof : D.dim -> DimProbe.t -> D.cof -> D.cof CM.m =
  fun r x phi ->
  let open CM in
  con_to_cof @<< push_subst_con r x @@ D.cof_to_con phi

and subst_clo : D.dim -> DimProbe.t -> D.tm_clo -> D.tm_clo CM.m =
  fun r x (Clo (tm, env)) ->
  let open CM in
  let+ env = subst_env r x env in
  D.Clo (tm, env)

and subst_tp_clo : D.dim -> DimProbe.t -> D.tp_clo -> D.tp_clo CM.m =
  fun r x (Clo (tp, env)) ->
  let open CM in
  let+ env = subst_env r x env in
  D.Clo (tp, env)

and subst_tele_clo : D.dim -> DimProbe.t -> D.tele_clo -> D.tele_clo CM.m =
  fun r x (Clo (sign, env)) ->
  let open CM in
  let+ env = subst_env r x env in
  D.Clo (sign, env)

and subst_kan_tele_clo : D.dim -> DimProbe.t -> D.kan_tele_clo -> D.kan_tele_clo CM.m =
  fun r x (Clo (sign, env)) ->
  let open CM in
  let+ env = subst_env r x env in
  D.Clo (sign, env)

and subst_env : D.dim -> DimProbe.t -> D.env -> D.env CM.m =
  fun r x {tpenv; conenv} ->
  let open CM in
  let+ tpenv = MU.map_bwd (subst_tp r x) tpenv
  and+ conenv = MU.map_bwd (subst_con r x) conenv in
  D.{tpenv; conenv}

and subst_tele : D.dim -> DimProbe.t -> D.tele -> D.tele CM.m =
  fun r x ->
  let open CM in
  function
  | D.Cell (ident, tp, clo) ->
    let+ tp = subst_tp r x tp
    and+ clo = subst_tele_clo r x clo in
    D.Cell (ident, tp, clo)
  | D.Empty -> ret D.Empty

and subst_kan_tele : D.dim -> DimProbe.t -> D.kan_tele -> D.kan_tele CM.m =
  fun r x ->
  let open CM in
  function
  | D.KCell (ident, code, clo) ->
    let+ code = subst_con r x code
    and+ clo = subst_kan_tele_clo r x clo in
    D.KCell (ident, code, clo)
  | D.KEmpty -> ret D.KEmpty

and subst_tp : D.dim -> DimProbe.t -> D.tp -> D.tp CM.m =
  fun r x ->
  let open CM in
  function
  | D.Pi (base, ident, fam) ->
    let+ base = subst_tp r x base
    and+ fam = subst_tp_clo r x fam in
    D.Pi (base, ident, fam)
  | D.Sg (base, ident, fam) ->
    let+ base = subst_tp r x base
    and+ fam = subst_tp_clo r x fam in
    D.Sg (base, ident, fam)
  | D.Signature tele ->
    let+ tele = subst_tele r x tele in
    D.Signature tele
  | D.Sub (base, phi, clo) ->
    let+ base = subst_tp r x base
    and+ phi = subst_cof r x phi
    and+ clo = subst_clo r x clo in
    D.Sub (base, phi, clo)
  | D.Univ | D.Nat | D.Circle | D.TpDim | D.TpCof as con -> ret con
  | D.TpPrf phi ->
    let+ phi = subst_cof r x phi in
    D.TpPrf phi
  | D.ElStable code ->
    let+ code = subst_stable_code r x code in
    D.ElStable code
  | D.ElCut cut ->
    let+ cut = subst_cut r x cut in
    D.ElCut cut
  | D.ElUnstable (`HCom (s, s', phi, bdy)) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ bdy = subst_con r x bdy in
    D.ElUnstable (`HCom (s, s', phi, bdy))
  | D.ElUnstable (`V (s, pcode, code, pequiv)) ->
    let+ s = subst_dim r x s
    and+ pcode = subst_con r x pcode
    and+ code = subst_con r x code
    and+ pequiv = subst_con r x pequiv in
    D.ElUnstable (`V (s, pcode, code, pequiv))
  | D.TpSplit branches ->
    let subst_branch (phi, clo) =
      let+ phi = subst_cof r x phi
      and+ clo = subst_tp_clo r x clo in
      phi, clo
    in
    let+ branches = MU.map subst_branch branches in
    D.TpSplit branches

and subst_stable_code : D.dim -> DimProbe.t -> D.con D.stable_code -> D.con D.stable_code CM.m =
  fun r x ->
  let open CM in
  function
  | `Pi (con0, con1) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1 in
    `Pi (con0, con1)
  | `Sg (con0, con1) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1 in
    `Sg (con0, con1)
  | `Signature tele ->
    let+ tele = subst_kan_tele r x tele in
    `Signature tele
  | `Ext (n, code, `Global cof, con) ->
    let+ code = subst_con r x code
    and+ con = subst_con r x con in
    `Ext (n, code, `Global cof, con)
  | `Nat | `Circle | `Univ as code ->
    ret code

and subst_cut : D.dim -> DimProbe.t -> D.cut -> D.cut CM.m =
  fun r x (hd, sp) ->
  let open CM in
  let+ hd = subst_hd r x hd
  and+ sp = subst_sp r x sp in
  (hd, sp)

and subst_hd : D.dim -> DimProbe.t -> D.hd -> D.hd CM.m =
  fun r x ->
  let open CM in
  function
  | D.Global _ | D.Var _ as hd -> ret hd
  | D.Coe (code, s, s', con) ->
    let+ code = subst_con r x code
    and+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ con = subst_con r x con in
    D.Coe (code, s, s', con)
  | D.UnstableCut (cut, ufrm) ->
    let+ cut = subst_cut r x cut
    and+ ufrm = subst_unstable_frm r x ufrm in
    D.UnstableCut(cut, ufrm)

and subst_unstable_frm : D.dim -> DimProbe.t -> D.unstable_frm -> D.unstable_frm CM.m =
  fun r x ->
  let open CM in
  function
  | D.KHCom (s, s', phi, bdy) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ bdy = subst_con r x bdy in
    D.KHCom (s, s', phi, bdy)
  | D.KCap (s, s', phi, code) ->
    let+ code = subst_con r x code
    and+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi in
    D.KCap (s, s', phi, code)
  | D.KVProj (s, pcode, code, pequiv) ->
    let+ s = subst_dim r x s
    and+ pcode = subst_con r x pcode
    and+ code = subst_con r x code
    and+ pequiv = subst_con r x pequiv in
    D.KVProj (s, pcode, code, pequiv)
  | D.KSubOut (phi, clo) ->
    let+ phi = subst_cof r x phi
    and+ clo = subst_clo r x clo in
    D.KSubOut (phi, clo)

and subst_frm : D.dim -> DimProbe.t -> D.frm -> D.frm CM.m =
  fun r x ->
  let open CM in
  function
  | D.KFst | D.KSnd | D.KElOut | D.KProj _ as frm -> ret frm
  | D.KAp (tp, arg) ->
    let+ tp = subst_tp r x tp
    and+ arg = subst_con r x arg in
    D.KAp (tp, arg)
  | D.KNatElim (con0, con1, con2) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1
    and+ con2 = subst_con r x con2 in
    D.KNatElim (con0, con1, con2)
  | D.KCircleElim (con0, con1, con2) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1
    and+ con2 = subst_con r x con2 in
    D.KCircleElim (con0, con1, con2)


and subst_sp : D.dim -> DimProbe.t -> D.frm list -> D.frm list CM.m =
  fun r x ->
  CM.MU.map @@ subst_frm r x

and eval_tele : S.tele -> D.tele EvM.m =
  let open EvM in
  function
  | S.ElTele tele ->
    let* tele = eval_kan_tele tele in
    lift_cmp @@ unfold_kan_tele tele
  | S.Cell (ident, tp, tele) ->
    let+ env = read_local
    and+ vtp = eval_tp tp in
    D.Cell (ident, vtp, D.Clo (tele, env))
  | S.Empty -> ret D.Empty

and eval_kan_tele : S.kan_tele -> D.kan_tele EvM.m =
  let open EvM in
  function
  | S.KCell (ident, code, tele) ->
    let+ env = read_local
    and+ vcode = eval code in
    D.KCell (ident, vcode, D.Clo (tele, env))
  | S.KEmpty -> ret D.KEmpty

and eval_tp : S.tp -> D.tp EvM.m =
  let open EvM in
  function
  | S.Nat -> ret D.Nat
  | S.Circle -> ret D.Circle
  | S.Pi (base, ident, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Pi (vbase, ident, D.Clo (fam, env))
  | S.Sg (base, ident, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Sg (vbase, ident, D.Clo (fam, env))
  | S.Signature sign ->
    let+ vsign = eval_tele sign in
    D.Signature vsign
  | S.Univ ->
    ret D.Univ
  | S.El tm ->
    let* con = eval tm in
    lift_cmp @@ do_el con
  | S.Sub (tp, tphi, tm) ->
    let+ env = read_local
    and+ tp = eval_tp tp
    and+ phi = eval_cof tphi in
    D.Sub (tp, phi, D.Clo (tm, env))
  | S.TpDim  ->
    ret D.TpDim
  | S.TpCof ->
    ret D.TpCof
  | S.TpPrf tphi ->
    let+ phi = eval_cof tphi in
    D.TpPrf phi
  | S.TpVar ix ->
    get_local_tp ix
  | S.TpCofSplit branches ->
    let tphis, tps = List.split branches in
    let* phis = MU.map eval_cof tphis in
    let+ env = read_local in
    let pclos = List.map (fun tp -> D.Clo (tp, env)) tps in
    D.TpSplit (List.combine phis pclos)
  | S.TpESub (sb, tp) ->
    eval_sub sb @@ eval_tp tp

and eval : S.t -> D.con EvM.m =
  let open EvM in
  let module K = Kado.Syntax in
  fun tm ->
    match tm with
    | S.Var i ->
      let* con = get_local i in
      lift_cmp @@ whnf_inspect_con con
    | S.Global sym ->
      let* st = EvM.read_global in
      let tp = RefineState.get_global sym st in
      ret @@ D.Cut {tp; cut = (D.Global sym, [])}
    | S.Let (def, _, body) ->
      let* vdef = eval def in
      append [vdef] @@ eval body
    | S.Ann (term, _) ->
      eval term
    | S.Zero ->
      ret D.Zero
    | S.Suc t ->
      let+ con = eval t in
      D.Suc con
    | S.NatElim (mot, zero, suc, n) ->
      let* vmot = eval mot in
      let* vzero = eval zero in
      let* vn = eval n in
      let* vsuc = eval suc in
      lift_cmp @@ do_nat_elim vmot vzero vsuc vn
    | S.Base ->
      ret D.Base
    | S.Loop tr ->
      let* r = eval_dim tr in
      begin
        CM.test_sequent [] (CofBuilder.boundary r) |> lift_cmp |>> function
        | true ->
          ret D.Base
        | false ->
          ret (D.Loop r)
      end
    | S.CircleElim (mot, base, loop, c) ->
      let* vmot = eval mot in
      let* vbase = eval base in
      let* vc = eval c in
      let* vloop = eval loop in
      lift_cmp @@ do_circle_elim vmot vbase vloop vc
    | S.Lam (ident, t) ->
      let+ env = read_local in
      D.Lam (ident, D.Clo (t, env))
    | S.Ap (t0, t1) ->
      let* con0 = eval t0 in
      let* con1 = eval t1 in
      lift_cmp @@ do_ap con0 con1
    | S.Pair (t1, t2) ->
      let+ el1 = eval t1
      and+ el2 = eval t2 in
      D.Pair (el1, el2)
    | S.Fst t ->
      let* con = eval t in
      lift_cmp @@ do_fst con
    | S.Snd t ->
      let* con = eval t in
      lift_cmp @@ do_snd con
    | S.Struct fields ->
      let+ fields = eval_fields fields in
      D.Struct fields
    | S.Proj (t, lbl, ix) ->
      let* con = eval t in
      lift_cmp @@ do_proj con lbl ix
    | S.Coe (tpcode, tr, tr', tm) ->
      let* r = eval_dim tr in
      let* r' = eval_dim tr' in
      let* con = eval tm in
      let psi, bdry = Splice.Bdry.coe ~r ~r' ~bdy:con in
      begin
        lift_cmp (CM.test_sequent [] psi) |>> function
        | true -> lift_cmp @@ splice_tm bdry
        | false ->
          let* coe_abs = eval tpcode in
          lift_cmp @@ do_rigid_coe coe_abs r r' con
      end
    | S.HCom (tpcode, tr, tr', tphi, tm) ->
      let* r = eval_dim tr in
      let* r' = eval_dim tr' in
      let* phi = eval_cof tphi in
      let* bdy = eval tm in
      let psi, bdry = Splice.Bdry.hcom ~r ~r' ~phi ~bdy in
      begin
        lift_cmp (CM.test_sequent [] psi) |>> function
        | true -> lift_cmp @@ splice_tm bdry
        | false ->
          let* vtpcode = eval tpcode in
          lift_cmp @@ do_rigid_hcom vtpcode r r' phi bdy
      end
    | S.Com (tpcode, tr, tr', tphi, tm) ->
      let* r = eval_dim tr in
      let* r' = eval_dim tr' in
      let* phi = eval_cof tphi in
      let* bdy = eval tm in
      let psi, bdry = Splice.Bdry.com ~r ~r' ~phi ~bdy in
      begin
        lift_cmp (CM.test_sequent [] psi) |>> function
        | true -> lift_cmp @@ splice_tm bdry
        | false ->
          let* vtpcode = eval tpcode in
          lift_cmp @@ do_rigid_com vtpcode r r' phi bdy
      end
    | S.SubOut tm ->
      let* con = eval tm in
      lift_cmp @@ do_sub_out con
    | S.SubIn tm ->
      let+ con = eval tm in
      D.SubIn con
    | S.ElOut tm ->
      let* con = eval tm in
      lift_cmp @@ do_el_out con
    | S.ElIn tm ->
      let+ con = eval tm in
      D.ElIn con
    | S.Dim0 -> ret D.Dim0
    | S.Dim1 -> ret D.Dim1
    | S.Cof cof_f ->
      begin
        match cof_f with
        | K.Le (tr, ts) ->
          let+ r = eval tr
          and+ s = eval ts in
          D.CofBuilder.le r s
        | K.Join tphis ->
          let+ phis = MU.map eval tphis in
          D.CofBuilder.join phis
        | K.Meet tphis ->
          let+ phis = MU.map eval tphis in
          D.CofBuilder.meet phis
      end
    | S.ForallCof tm ->
      let sym = DimProbe.fresh () in
      let i = Dim.DimProbe sym in
      let+ phi = append [D.dim_to_con i] @@ eval_cof tm in
      D.cof_to_con @@ CofBuilder.forall (i, phi)
    | S.CofSplit (branches) ->
      let tphis, tms = List.split branches in
      let* phis = MU.map eval_cof tphis in
      let+ env = read_local in
      let pclos = List.map (fun tm -> D.Clo (tm, env)) tms in
      D.Split (List.combine phis pclos)
    | S.Prf ->
      ret D.Prf

    | S.CodeExt (n, fam, `Global phi, bdry) ->
      let* phi = drop_all_cons @@ eval phi in
      let* fam = eval fam in
      let* bdry = eval bdry in
      ret @@ D.StableCode (`Ext (n, fam, `Global phi, bdry))

    | S.CodePi (base, fam) ->
      let+ vbase = eval base
      and+ vfam = eval fam in
      D.StableCode (`Pi (vbase, vfam))

    | S.CodeSg (base, fam) ->
      let+ vbase = eval base
      and+ vfam = eval fam in
      D.StableCode (`Sg (vbase, vfam))

    | S.CodeSignature tele ->
      let+ tele = eval_kan_tele tele in
      D.StableCode (`Signature tele)

    | S.CodeNat ->
      ret @@ D.StableCode `Nat

    | S.CodeCircle ->
      ret @@ D.StableCode `Circle

    | S.CodeUniv ->
      ret @@ D.StableCode `Univ

    | S.Box (r, s, phi, sides, cap) ->
      let+ vr = eval_dim r
      and+ vs = eval_dim s
      and+ vphi = eval_cof phi
      and+ vsides = eval sides
      and+ vcap = eval cap in
      D.Box (vr, vs, vphi, vsides, vcap)

    | S.Cap (r, s, phi, code, box) ->
      let* vr = eval_dim r in
      let* vs = eval_dim s in
      let* vphi = eval_cof phi in
      let* vcode = eval code in
      let* vbox = eval box in
      let psi, bdry = Splice.Bdry.cap ~r:vr ~r':vs ~phi:vphi ~code:vcode ~box:vbox in
      lift_cmp @@
      begin
        let open CM in
        CM.test_sequent [] psi |>>
        function
        | true -> splice_tm bdry
        | false -> do_rigid_cap vr vs vphi vcode vbox
      end

    | S.VIn (r, equiv, pivot, base) ->
      let+ vr = eval_dim r
      and+ vequiv = eval equiv
      and+ vpivot = eval pivot
      and+ vbase = eval base in
      D.VIn (vr, vequiv, vpivot, vbase)

    | S.VProj (r, pcode, code, pequiv, v) ->
      let* vr = eval_dim r in
      let* vv = eval v in
      let* vpcode = eval pcode in
      let* vcode = eval code in
      let* vpequiv = eval pequiv in
      let psi, bdry = Splice.Bdry.vproj ~r:vr ~pcode:vpcode ~code:vcode ~pequiv:vpequiv ~v:vv in
      lift_cmp @@
      begin
        let open CM in
        CM.test_sequent [] psi |>> function
        | true -> splice_tm bdry
        | false -> do_rigid_vproj vr vpcode vcode vpequiv vv
      end

    | S.CodeV (r, pcode, code, pequiv) ->
      let+ vr = eval_dim r
      and+ vpcode = eval pcode
      and+ vcode = eval code
      and+ vpequiv = eval pequiv in
      D.UnstableCode (`V (vr, vpcode, vcode, vpequiv))

    | S.ESub (sb, tm) ->
      eval_sub sb @@ eval tm

and eval_fields : S.fields -> D.fields EvM.m =
  let open EvM in
  function
  | S.Fields fields ->
    let+ fields = MU.map (MU.second eval) fields in
    D.Fields fields
  | S.Unpack (lbls, tm) ->
    let* vtm = eval tm in
    lift_cmp @@ do_unpack lbls vtm
  | S.MCoe (_, lines, r, s, fields) ->
    let* env = read_local in
    let lines = D.Clo (lines, env) in
    let* r = eval_dim r in
    let* s = eval_dim s in
    let* fields = eval_fields fields in
    lift_cmp @@ do_rigid_mcoe lines r s fields
  | S.MCom (tele, r, s, phi, bdys) ->
    let* tele = eval_kan_tele tele in
    let* r = eval_dim r in
    let* s = eval_dim s in
    let* phi = eval_cof phi in
    let* bdys = eval_fields bdys in
    lift_cmp @@ do_rigid_mcom tele r s phi bdys

and eval_sub : 'a. S.sub -> 'a EvM.m -> 'a EvM.m =
  fun sb kont ->
  let open EvM in
  match sb with
  | S.Sb1 ->
    drop_all_cons kont
  | S.SbP ->
    drop_con kont
  | S.SbI -> kont
  | S.SbE (sb, tm) ->
    let* con = eval tm in
    append [con] @@ eval_sub sb kont
  | S.SbC (sb0, sb1) ->
    eval_sub sb0 @@ eval_sub sb1 kont

and eval_dim tr =
  let open EvM in
  let* con = eval tr in
  lift_cmp @@ con_to_dim con

and eval_cof tphi =
  let open EvM in
  let* vphi = eval tphi in
  lift_cmp @@ con_to_cof vphi


and whnf_con : D.con -> D.con whnf CM.m =
  let open CM in
  function
  | D.Lam _ | D.BindSym _ | D.Zero | D.Suc _ | D.Base | D.Pair _ | D.Struct _ | D.SubIn _ | D.ElIn _
  | D.Cof _ | D.Dim0 | D.Dim1 | D.Prf | D.StableCode _ | D.DimProbe _ ->
    ret `Done
  | D.LetSym (r, x, con) ->
    reduce_to @<< push_subst_con r x con
  | D.Cut {cut; _} ->
    whnf_cut cut
  | D.FHCom (_, r, r', phi, bdy) ->
    whnf_boundary @@ Splice.Bdry.hcom ~r ~r' ~phi ~bdy
  | D.Box (r, r', phi, sides, cap) ->
    whnf_boundary @@ Splice.Bdry.box ~r ~r' ~phi ~sides ~cap
  | D.UnstableCode code ->
    whnf_boundary @@ Splice.Bdry.unstable_code code
  | D.VIn (r, _pequiv, pivot, base) ->
    whnf_boundary @@ Splice.Bdry.vin ~r ~pivot ~base
  | D.Loop r ->
    begin
      test_sequent [] (CofBuilder.boundary r) |>>
      function
      | true -> ret (`Reduce D.Base)
      | false -> ret `Done
    end
  | D.Split branches -> whnf_con_branches branches

and whnf_con_branches =
  let open CM in
  function
  | [] -> ret `Done
  | (phi, clo) :: branches ->
    test_sequent [] phi |>> function
    | true ->
      reduce_to @<< inst_tm_clo clo D.Prf
    | false ->
      whnf_con_branches branches

and whnf_tp_branches =
  let open CM in
  function
  | [] -> ret `Done
  | (phi, clo) :: branches ->
    test_sequent [] phi |>> function
    | true ->
      reduce_to_tp @<< inst_tp_clo clo D.Prf
    | false ->
      whnf_tp_branches branches

and whnf_boundary (psi, bdry) =
  let open CM in
  test_sequent [] psi |>>
  function
  | true -> reduce_to @<< splice_tm bdry
  | false -> ret `Done

and reduce_to con =
  let open CM in
  whnf_con con |>> function
  | `Done -> ret @@ `Reduce con
  | `Reduce con -> ret @@ `Reduce con

and reduce_to_tp tp =
  let open CM in
  whnf_tp tp |>> function
  | `Done -> ret @@ `Reduce tp
  | `Reduce tp -> ret @@ `Reduce tp


and plug_into sp con =
  let open CM in
  let* res = do_spine con sp in
  whnf_con res |>> function
  | `Done -> ret @@ `Reduce res
  | `Reduce res -> ret @@ `Reduce res

and whnf_hd hd =
  let open CM in
  match hd with
  | D.Global _ -> ret `Done
  | D.Var _ -> ret `Done
  | D.Coe (abs, r, s, con) ->
    begin
      test_sequent [] (CofBuilder.eq r s) |>> function
      | true -> reduce_to con
      | false ->
        begin
          dispatch_rigid_coe abs |>>
          function
          | `Done ->
            ret `Done
          | `Reduce tag ->
            reduce_to @<< enact_rigid_coe abs r s con tag
        end
    end
  | D.UnstableCut (cut, ufrm) ->
    let phi, bdry = Splice.Bdry.unstable_frm cut ufrm in
    test_sequent [] phi |>>
    function
    | true ->
      reduce_to @<< splice_tm bdry
    | false ->
      whnf_cut cut |>>
      function
      | `Done ->
        ret `Done
      | `Reduce con ->
        reduce_to @<< do_rigid_unstable_frm con ufrm

and do_rigid_unstable_frm con ufrm =
  match ufrm with
  | D.KHCom (r, s, phi, bdy) ->
    do_rigid_hcom con r s phi bdy
  | D.KCap (r, s, phi, code) ->
    do_rigid_cap r s phi code con
  | D.KVProj (r, pcode, code, pequiv) ->
    do_rigid_vproj r pcode code pequiv con
  | D.KSubOut _ ->
    do_sub_out con

and whnf_cut : D.cut -> D.con whnf CM.m =
  let open CM in
  fun (hd, sp) ->
    whnf_hd hd |>>
    function
    | `Done -> ret `Done
    | `Reduce con -> plug_into sp con

and whnf_tp =
  let open CM in
  function
  | D.ElCut cut ->
    begin
      whnf_cut cut |>>
      function
      | `Done ->
        ret `Done
      | `Reduce con ->
        reduce_to_tp @<< do_el con
    end
  | D.ElUnstable code ->
    let phi, bdry = Splice.Bdry.unstable_code code in
    begin
      test_sequent [] phi |>> function
      | true -> reduce_to_tp @<< do_el @<< splice_tm bdry
      | false -> ret `Done
    end
  | D.TpSplit branches -> whnf_tp_branches branches
  | _tp ->
    ret `Done

and whnf_tp_ tp =
  let open CM in
  whnf_tp tp |>>
  function
  | `Done -> ret tp
  | `Reduce tp -> ret tp

and whnf_con_ con =
  let open CM in
  whnf_con con |>>
  function
  | `Done -> ret con
  | `Reduce con -> ret con

and do_nat_elim (mot : D.con) zero (suc : D.con) : D.con -> D.con CM.m =
  let open CM in

  let rec go con =
    whnf_inspect_con con |>>
    function
    | D.Zero ->
      ret zero
    | D.Suc con' ->
      let* v = go con' in
      do_ap2 suc con' v
    | D.Cut {cut; _} as con ->
      let* fib = do_ap mot con in
      let+ elfib = do_el fib in
      cut_frm ~tp:elfib ~cut @@
      D.KNatElim (mot, zero, suc)
    | D.FHCom (`Nat, r, s, phi, bdy) ->
      (* bdy : (i : 𝕀) (_ : [_]) → nat *)
      splice_tm @@
      Splice.con mot @@ fun mot ->
      Splice.dim r @@ fun r ->
      Splice.dim s @@ fun s ->
      Splice.cof phi @@ fun phi ->
      Splice.con bdy @@ fun bdy ->
      Splice.con zero @@ fun zero ->
      Splice.con suc @@ fun suc ->
      Splice.term @@
      let fam =
        TB.lam @@ fun i ->
        let fhcom =
          TB.el_out @@
          TB.hcom TB.code_nat r i phi @@
          TB.lam @@ fun j ->
          TB.lam @@ fun prf ->
          TB.el_in @@ TB.ap bdy [j; prf]
        in
        TB.ap mot [fhcom]
      in
      let bdy' =
        TB.lam @@ fun i ->
        TB.lam @@ fun prf ->
        TB.nat_elim mot zero suc @@ TB.ap bdy [i; prf]
      in
      TB.com fam r s phi bdy'
    | D.Split branches as con ->
      splice_tm @@
      Splice.con mot @@ fun mot ->
      Splice.con zero @@ fun zero ->
      Splice.con suc @@ fun suc ->
      Splice.Macro.commute_split con (List.map fst branches) @@ TB.nat_elim mot zero suc
    | con ->
      Format.eprintf "bad nat-elim: %a@." D.pp_con con;
      CM.throw @@ NbeFailed "Not a number"

  in
  fun con ->
    abort_if_inconsistent (ret D.tm_abort) @@
    go con

and do_circle_elim (mot : D.con) base (loop : D.con) c : D.con CM.m =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  whnf_inspect_con c |>>
  function
  | D.Base ->
    ret base
  | D.Loop r ->
    do_ap loop (D.dim_to_con r)
  | D.Cut {cut; _} as c ->
    let* fib = do_ap mot c in
    let+ elfib = do_el fib in
    cut_frm ~tp:elfib ~cut @@
    D.KCircleElim (mot, base, loop)
  | D.FHCom (`Circle, r, s, phi, bdy) ->
    splice_tm @@
    Splice.con mot @@ fun mot ->
    Splice.dim r @@ fun r ->
    Splice.dim s @@ fun s ->
    Splice.cof phi @@ fun phi ->
    Splice.con bdy @@ fun bdy ->
    Splice.con base @@ fun base ->
    Splice.con loop @@ fun loop ->
    Splice.term @@
    let fam =
      TB.lam @@ fun i ->
      let fhcom =
        TB.el_out @@
        TB.hcom TB.code_circle r i phi @@
        TB.lam @@ fun j ->
        TB.lam @@ fun prf ->
        TB.el_in @@ TB.ap bdy [j; prf]
      in
      TB.ap mot [fhcom]
    in
    let bdy' =
      TB.lam @@ fun i ->
      TB.lam @@ fun prf ->
      TB.circle_elim mot base loop @@ TB.ap bdy [i; prf]
    in
    TB.com fam r s phi bdy'
  | D.Split branches as con ->
    splice_tm @@
    Splice.con mot @@ fun mot ->
    Splice.con base @@ fun base ->
    Splice.con loop @@ fun loop ->
    Splice.Macro.commute_split con (List.map fst branches) @@ TB.circle_elim mot base loop
  | c ->
    Format.eprintf "bad circle-elim: %a@." D.pp_con c;
    CM.throw @@ NbeFailed "Not an element of the circle"

and inst_tp_clo : D.tp_clo -> D.con -> D.tp CM.m =
  fun clo x ->
  match clo with
  | Clo (bdy, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@
    eval_tp bdy

and inst_tm_clo : D.tm_clo -> D.con -> D.con CM.m =
  fun clo x ->
  match clo with
  | D.Clo (bdy, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@
    eval bdy

and inst_tele_clo : D.tele_clo -> D.con -> D.tele CM.m =
  fun clo x ->
  match clo with
  | D.Clo (tele, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@ eval_tele tele

and inst_kan_tele_clo : D.kan_tele_clo -> D.con -> D.kan_tele CM.m =
  fun clo x ->
  match clo with
  | D.Clo (tele, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@ eval_kan_tele tele

and inst_tele : D.tele -> D.con -> D.tele CM.m =
  fun tele x ->
  match tele with
  | D.Cell (_, _, clo) ->
    inst_tele_clo clo x
  | D.Empty ->
    CM.throw @@ NbeFailed "Tried to instantiate empty telescope"

and inst_kan_tele : D.kan_tele -> D.con -> D.kan_tele CM.m =
  fun tele x ->
  match tele with
  | D.KCell (_, _, clo) ->
    inst_kan_tele_clo clo x
  | D.KEmpty ->
    CM.throw @@ NbeFailed "Tried to instantiate empty telescope"

(* reduces a constructor to something that is stable to pattern match on *)
and whnf_inspect_con con =
  let open CM in
  whnf_con con |>>
  function
  | `Done -> ret con
  | `Reduce con' -> ret con'

(* reduces a constructor to something that is stable to pattern match on,
 * _including_ type annotations on cuts *)
and inspect_con con =
  let open CM in
  whnf_inspect_con con |>>
  function
  | D.Cut {tp; cut} as con ->
    begin
      whnf_tp tp |>>
      function
      | `Done -> ret con
      | `Reduce tp -> ret @@ D.Cut {tp; cut}
    end
  | con -> ret con


and do_fst con : D.con CM.m =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis = splice_tm @@ Splice.Macro.commute_split con phis TB.fst in
  begin
    inspect_con con |>>
    function
    | D.Pair (con0, _) -> ret con0
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.Sg (base, _, _); cut} ->
      ret @@ cut_frm ~tp:base ~cut D.KFst
    | _ ->
      throw @@ NbeFailed "Couldn't fst argument in do_fst"
  end


and do_snd con : D.con CM.m =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis = splice_tm @@ Splice.Macro.commute_split con phis TB.snd in
  begin
    inspect_con con |>>
    function
    | D.Pair (_, con1) -> ret con1
    | D.Split branches ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.Sg (_, _, fam); cut} ->
      let* fst = do_fst con in
      let+ fib = inst_tp_clo fam fst in
      cut_frm ~tp:fib ~cut D.KSnd
    | _ ->
      throw @@ NbeFailed ("Couldn't snd argument in do_snd")
  end

and cut_frm_tele (cut : D.cut) (tele : D.tele) (ix : int) =
  let open CM in
  let rec go n =
    function
    | D.Cell (flbl, tp, _) when n = ix ->
      ret @@ cut_frm ~tp ~cut (D.KProj (flbl, ix))
    | D.Cell (flbl, tp, clo) ->
      let field = cut_frm ~tp ~cut (D.KProj (flbl, n)) in
      let* tele = inst_tele_clo clo field in
      go (n + 1) tele
    | D.Empty ->
      throw @@ NbeFailed ("Couldn't find field label in cut_frm_sign")
  in go 0 tele

and proj_field (fields : D.fields) (ix : int) : D.con CM.m =
  let open CM in
  match fields with
  | D.Fields fields ->
    ret @@ snd @@ List.nth fields ix

and do_proj (con : D.con) (lbl : Ident.t) (ix : int) : D.con CM.m =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis = splice_tm @@ Splice.Macro.commute_split con phis (fun tm -> TB.proj tm lbl ix) in
  begin
    inspect_con con |>>
    function
    | D.Struct fields ->
      proj_field fields ix
    | D.Split branches ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.Signature sign; cut} ->
      cut_frm_tele cut sign ix
    | _ ->
      throw @@ NbeFailed ("Couldn't proj argument in do_proj")
  end

and do_unpack (lbls : Ident.t list) (con : D.con) : D.fields CM.m =
  let open CM in
  let rec unpack_eta fields n =
    function
    | lbl :: lbls ->
      let* field = do_proj con lbl n in
      unpack_eta (fields #< (lbl, field)) (n + 1) lbls
    | [] ->
      ret @@ D.Fields (Bwd.to_list fields)
  in
  match con with
  | D.Struct fields -> ret @@ fields
  | _ -> unpack_eta Emp 0 lbls

and do_aps (con : D.con) (args : D.con list) : D.con CM.m =
  let open CM in
  MU.fold_left_m (fun arg f -> do_ap f arg) con args

and do_ap2 f a b =
  let open CM in
  let* fa = do_ap f a in
  do_ap fa b


and do_ap con arg =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis =
    splice_tm @@
    Splice.con arg @@ fun arg ->
    Splice.Macro.commute_split con phis @@ fun f -> TB.ap f [arg]
  in
  begin
    inspect_con con |>>
    function
    | D.Lam (_, clo) ->
      inst_tm_clo clo arg

    | D.BindSym (x, conx) as con ->
      begin
        match arg with
        | D.Split branches ->
          splitter con @@ List.map fst branches
        | _ ->
          let* r = con_to_dim arg in
          subst_con r x conx
      end

    | D.Cut {tp = D.Pi (base, _, fam); cut} ->
      let+ fib = inst_tp_clo fam arg in
      cut_frm ~tp:fib ~cut @@ D.KAp (base, arg)

    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches

    | D.Split branches ->
      splitter con @@ List.map fst branches

    | con ->
      Format.eprintf "bad function: %a / %a@." D.pp_con con D.pp_con arg;
      throw @@ NbeFailed "Not a function in do_ap"
  end


and do_sub_out con =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis =
    splice_tm @@ Splice.Macro.commute_split con phis TB.sub_out
  in
  begin
    inspect_con con |>>
    function
    | D.SubIn con ->
      ret con
    | D.Cut {tp = D.Sub (tp, phi, clo); cut} ->
      ret @@ D.Cut {tp; cut = D.UnstableCut (cut, D.KSubOut (phi, clo)), []}
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | con ->
      Format.eprintf "bad sub_out: %a@." D.pp_con con;
      throw @@ NbeFailed "do_sub_out"
  end


and do_rigid_cap r s phi code box =
  let splitter con phis =
    splice_tm @@
    Splice.dim r @@ fun r ->
    Splice.dim s @@ fun s ->
    Splice.cof phi @@ fun phi ->
    Splice.con code @@ fun code ->
    Splice.Macro.commute_split con phis @@ TB.cap r s phi code
  in
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  begin
    inspect_con box |>>
    function
    | D.Box (_,_,_,_,cap) ->
      ret cap
    | D.Cut {cut; tp = D.ElUnstable (`HCom (r, s, phi, code))} ->
      let* code_fib = do_ap2 code (D.dim_to_con r) D.Prf in
      let* tp = do_el code_fib in
      ret @@ D.Cut {tp; cut = D.UnstableCut (cut, D.KCap (r, s, phi, code)), []}
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | _ ->
      throw @@ NbeFailed "do_rigid_cap"
  end

and do_rigid_vproj r pcode code pequiv v =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis =
    splice_tm @@
    Splice.dim r @@ fun r ->
    Splice.con pcode @@ fun pcode ->
    Splice.con code @@ fun code ->
    Splice.con pequiv @@ fun pequiv ->
    Splice.Macro.commute_split con phis @@ TB.vproj r pcode code pequiv
  in
  begin
    inspect_con v |>>
    function
    | D.VIn (_, _, _, base) ->
      ret base
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.ElUnstable (`V (r, pcode, code, pequiv)); cut} ->
      let* tp = do_el code in
      ret @@ D.Cut {tp; cut = D.UnstableCut (cut, D.KVProj (r, pcode, code, pequiv)), []}
    | _ ->
      Format.eprintf "bad vproj: %a@." D.pp_con v;
      throw @@ NbeFailed "do_rigid_vproj"
  end

and do_el_out con =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis =
    splice_tm @@
    Splice.con con @@ fun tm ->
    Splice.cons (List.map D.cof_to_con phis) @@ fun phis ->
    Splice.term @@
    TB.cof_split @@ List.map (fun phi -> phi, TB.el_out tm) phis
  in
  begin
    inspect_con con |>>
    function
    | D.ElIn con ->
      ret con
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.ElStable code; cut} ->
      let+ tp = unfold_el code in
      cut_frm ~tp ~cut D.KElOut
    | _ ->
      Format.eprintf "bad el/out: %a@." D.pp_con con;
      throw @@ NbeFailed "do_el_out"
  end


and do_el : D.con -> D.tp CM.m =
  let open CM in
  fun con ->
    abort_if_inconsistent (ret D.tp_abort) @@
    let splitter con phis =
      splice_tp @@
      Splice.con con @@ fun tm ->
      Splice.cons (List.map D.cof_to_con phis) @@ fun phis ->
      Splice.term @@
      TB.tp_cof_split @@ List.map (fun phi -> phi, TB.el tm) phis
    in
    begin
      inspect_con con |>>
      function
      | D.UnstableCode code ->
        ret @@ D.ElUnstable code
      | D.Split branches as con ->
        splitter con @@ List.map fst branches
      | D.Cut {tp = D.TpSplit branches; _} as con ->
        splitter con @@ List.map fst branches
      | D.Cut {cut; tp = D.Univ} ->
        ret @@ D.ElCut cut
      | D.StableCode code ->
        ret @@ D.ElStable code
      | _ ->
        Format.eprintf "bad do_el: %a@." D.pp_con con;
        throw @@ NbeFailed "Invalid arguments to do_el"
    end

and unfold_el : D.con D.stable_code -> D.tp CM.m =
  let open CM in
  fun code ->
    abort_if_inconsistent (ret D.tp_abort) @@
    begin
      match code with
      | `Nat ->
        ret D.Nat

      | `Circle ->
        ret D.Circle

      | `Univ ->
        ret D.Univ

      | `Pi (base, fam) ->
        splice_tp @@
        Splice.con base @@ fun base ->
        Splice.con fam @@ fun fam ->
        Splice.term @@
        TB.pi (TB.el base) @@ fun x ->
        TB.el @@ TB.ap fam [x]

      | `Sg (base, fam) ->
        splice_tp @@
        Splice.con base @@ fun base ->
        Splice.con fam @@ fun fam ->
        Splice.term @@
        TB.sg (TB.el base) @@ fun x ->
        TB.el @@ TB.ap fam [x]
      | `Signature tele ->
        let+ tele = unfold_kan_tele tele in
        D.Signature tele
      | `Ext (n, fam, `Global phi, bdry) ->
        splice_tp @@
        Splice.con phi @@ fun phi ->
        Splice.con fam @@ fun fam ->
        Splice.con bdry @@ fun bdry ->
        Splice.term @@
        TB.cube n @@ fun js ->
        TB.sub (TB.el @@ TB.ap fam js) (TB.ap phi js) @@ fun _ ->
        TB.ap bdry @@ js @ [TB.prf]
    end

and unfold_kan_tele : D.kan_tele -> D.tele CM.m =
  let open CM in
  function
  | D.KCell (lbl, code, D.Clo (tele, env)) ->
    let+ tp = do_el code in
    D.Cell (lbl, tp, D.Clo (S.ElTele tele, env))
  | D.KEmpty ->
    ret D.Empty

and dispatch_rigid_coe line =
  let open CM in
  let go x codex =
    match codex with
    | D.StableCode codex ->
      ret @@ `Reduce (`Stable (x, codex))
    | D.UnstableCode code ->
      ret @@ `Reduce (`Unstable (x, code))
    | D.Split branches ->
      let* phis =
        branches |> MU.map @@ fun (phix, _) ->
        forall_cof (DimProbe x, phix)
      in
      ret @@ `Reduce (`Split phis)
    | D.Cut _ ->
      ret @@ `Done
    | _ ->
      ret @@ `Unknown
  in
  let peek line =
    let x = DimProbe.fresh () in
    go x @<< whnf_inspect_con @<< do_ap line @@ D.dim_to_con @@ Dim.DimProbe x |>>
    function
    | `Reduce _ | `Done as res -> ret res
    | `Unknown ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_coe"
  in
  match line with
  | D.BindSym (x, codex) ->
    begin
      go x codex |>>
      function
      | `Reduce _ | `Done as res -> ret res
      | `Unknown -> peek line
    end
  | _ ->
    peek line

and dispatch_rigid_hcom code =
  let open CM in
  let go code =
    match code with
    | D.StableCode code ->
      ret @@ `Reduce (`Stable code)
    | D.UnstableCode code ->
      ret @@ `Reduce (`Unstable code)
    | D.Cut {cut; _} ->
      ret @@ `Done cut
    | D.Split branches ->
      ret @@ `Reduce (`Split (List.map fst branches))
    | _ ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_hcom"
  in
  go @<< whnf_inspect_con code

and enact_rigid_coe line r r' con tag =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  match tag with
  | `Stable (x, code) ->
    begin
      match code with
      | `Nat | `Circle | `Univ -> ret con
      | `Pi (basex, famx) ->
        splice_tm @@
        Splice.con (D.BindSym (x, basex)) @@ fun base_line ->
        Splice.con (D.BindSym (x, famx)) @@ fun fam_line ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.con con @@ fun bdy ->
        Splice.term @@ TB.Kan.coe_pi ~base_line ~fam_line ~r ~r' ~bdy
      | `Sg (basex, famx) ->
        splice_tm @@
        Splice.con (D.BindSym (x, basex)) @@ fun base_line ->
        Splice.con (D.BindSym (x, famx)) @@ fun fam_line ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.con con @@ fun bdy ->
        Splice.term @@ TB.Kan.coe_sg ~base_line ~fam_line ~r ~r' ~bdy
      | `Signature telex ->
        let* fields = do_unpack (D.kan_tele_lbls telex) con in
        let+ coe_fields = enact_rigid_mcoe telex x r r' fields in
        D.Struct coe_fields
      | `Ext (n, famx, `Global cof, bdryx) ->
        splice_tm @@
        Splice.con cof @@ fun cof ->
        Splice.con (D.BindSym (x, famx)) @@ fun fam_line ->
        Splice.con (D.BindSym (x, bdryx)) @@ fun bdry_line ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.con con @@ fun bdy ->
        Splice.term @@ TB.Kan.coe_ext ~n ~cof ~fam_line ~bdry_line ~r ~r' ~bdy
    end
  | `Unstable (x, codex) ->
    begin
      match codex with
      | `HCom (sx, s'x, phix, bdyx) ->
        splice_tm @@
        Splice.con (D.BindSym (x, D.dim_to_con sx)) @@ fun s ->
        Splice.con (D.BindSym (x, D.dim_to_con s'x)) @@ fun s' ->
        Splice.con (D.BindSym (x, D.cof_to_con phix)) @@ fun phi ->
        Splice.con (D.BindSym (x, bdyx)) @@ fun code ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.con con @@ fun bdy ->
        let fhcom = TB.Kan.FHCom.{r = s; r' = s'; phi; bdy = code} in
        Splice.term @@ TB.Kan.FHCom.coe_fhcom ~fhcom ~r ~r' ~bdy
      | `V (s, pcode, code, pequiv) ->
        splice_tm @@
        Splice.con (D.BindSym (x, D.dim_to_con s)) @@ fun s ->
        Splice.con (D.BindSym (x, pcode)) @@ fun pcode ->
        Splice.con (D.BindSym (x, code)) @@ fun code ->
        Splice.con (D.BindSym (x, pequiv)) @@ fun pequiv ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.con con @@ fun bdy ->
        let v = TB.Kan.V.{r = s; pcode; code; pequiv} in
        Splice.term @@ TB.Kan.V.coe_v ~v ~r ~r' ~bdy
    end
  | `Split psis ->
    splice_tm @@
    Splice.dim r @@ fun r ->
    Splice.dim r' @@ fun r' ->
    Splice.con con @@ fun bdy ->
    Splice.con line @@ fun line  ->
    Splice.cons (List.map D.cof_to_con psis) @@ fun psis ->
    Splice.term @@
    let branch psi = psi, TB.coe line r r' bdy in
    TB.cof_split @@ List.map branch psis

and enact_rigid_mcoe linesx x r s fields =
  let open CM in
  let D.Fields fields = fields in
  let rec go acc linesx fields =
    match linesx, fields with
    | D.KCell (lbl, linex, linesx), (_, field) :: fields ->
      let* coe_field = do_rigid_coe (D.BindSym (x, linex)) r (Dim.DimProbe x) field in
      let* linesx = inst_kan_tele_clo linesx coe_field in
      go (acc #< (lbl, D.LetSym (s, x, coe_field))) linesx fields
    | D.KEmpty, [] ->
      ret @@ D.Fields (Bwd.to_list acc)
    | _ ->
      invalid_arg "bad do_rigid_mcoe: telescope/fields mismatch"
  in
  go Emp linesx fields

and enact_rigid_hcom code r r' phi bdy tag =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  match tag with
  | `Stable code ->
    begin
      match code with
      | `Pi (_, fam) ->
        splice_tm @@
        Splice.con fam @@ fun fam ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.cof phi @@ fun phi ->
        Splice.con bdy @@ fun bdy ->
        Splice.term @@
        TB.Kan.hcom_pi ~fam ~r ~r' ~phi ~bdy
      | `Sg (base, fam) ->
        splice_tm @@
        Splice.con base @@ fun base ->
        Splice.con fam @@ fun fam ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.cof phi @@ fun phi ->
        Splice.con bdy @@ fun bdy ->
        Splice.term @@
        TB.Kan.hcom_sg ~base ~fam ~r ~r' ~phi ~bdy
      | `Signature tele ->
        let rec go bdys =
          function
          | lbl :: lbls ->
            let* bdy =
              splice_tm @@
              Splice.con bdy @@ fun bdy ->
              Splice.term @@
              TB.lam @@ fun i ->
              TB.lam @@ fun prf ->
              TB.ap bdy [i; prf]
            in go (bdys #< (lbl, bdy)) lbls
          | [] ->
            ret @@ D.Fields (Bwd.to_list bdys)
        in
        let* bdys = go Emp (D.kan_tele_lbls tele) in
        let+ fields = do_rigid_mcom tele r r' phi bdys in
        D.ElIn (D.Struct fields)
      | `Ext (n, fam, `Global cof, bdry) ->
        splice_tm @@
        Splice.con cof @@ fun cof ->
        Splice.con fam @@ fun fam ->
        Splice.con bdry @@ fun bdry ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.cof phi @@ fun phi ->
        Splice.con bdy @@ fun bdy ->
        Splice.term @@
        TB.Kan.hcom_ext ~n ~cof ~fam ~bdry ~r ~r' ~phi ~bdy
      | `Circle | `Nat as tag ->
        let+ bdy' =
          splice_tm @@
          Splice.con bdy @@ fun bdy ->
          Splice.term @@
          TB.lam @@ fun i -> TB.lam @@ fun prf ->
          TB.el_out @@ TB.ap bdy [i; prf]
        in
        D.ElIn (D.FHCom (tag, r, r', phi, bdy'))
      | `Univ ->
        let+ bdy' =
          splice_tm @@
          Splice.con bdy @@ fun bdy ->
          Splice.term @@
          TB.lam @@ fun i -> TB.lam @@ fun prf ->
          TB.el_out @@ TB.ap bdy [i; prf]
        in
        D.ElIn (D.UnstableCode (`HCom (r, r', phi, bdy')))
    end
  | `Unstable code ->
    begin
      match code with
        `HCom (h_r,h_r',h_phi,h_bdy) ->
        splice_tm @@
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.cof phi @@ fun phi ->
        Splice.con bdy @@ fun bdy ->
        Splice.dim h_r @@ fun h_r ->
        Splice.dim h_r' @@ fun h_r' ->
        Splice.cof h_phi @@ fun h_phi ->
        Splice.con h_bdy @@ fun h_bdy ->
        Splice.term @@
        let fhcom = TB.Kan.FHCom.{r = h_r; r' = h_r'; phi = h_phi; bdy = h_bdy} in
        TB.Kan.FHCom.hcom_fhcom ~fhcom ~r ~r' ~phi ~bdy
      | `V (h_r,h_pcode,h_code,h_pequiv) ->
        splice_tm @@
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.cof phi @@ fun phi ->
        Splice.con bdy @@ fun bdy ->
        Splice.dim h_r @@ fun h_r ->
        Splice.con h_pcode @@ fun h_pcode ->
        Splice.con h_code @@ fun h_code ->
        Splice.con h_pequiv @@ fun h_pequiv ->
        Splice.term @@
        let v = TB.Kan.V.{r = h_r; pcode = h_pcode; code = h_code; pequiv = h_pequiv} in
        TB.Kan.V.hcom_v ~v ~r ~r' ~phi ~bdy
    end

  | `Split psis ->
    splice_tm @@
    Splice.dim r @@ fun r ->
    Splice.dim r' @@ fun r' ->
    Splice.cof phi @@ fun phi ->
    Splice.con bdy @@ fun bdy ->
    Splice.con code @@ fun code ->
    Splice.cons (List.map D.cof_to_con psis) @@ fun psis ->
    Splice.term @@
    let branch psi = psi, TB.hcom code r r' phi bdy in
    TB.cof_split @@ List.map branch psis

  | `Done cut ->
    let tp = D.ElCut cut in
    let hd = D.UnstableCut (cut, D.KHCom (r, r', phi, bdy)) in
    ret @@ D.Cut {tp; cut = hd, []}

and do_rigid_coe (line : D.con) r s con =
  let open CM in
  CM.abort_if_inconsistent (ret D.tm_abort) @@
  begin
    dispatch_rigid_coe line |>>
    function
    | `Done ->
      let hd = D.Coe (line, r, s, con) in
      let* code = do_ap line (D.dim_to_con s) in
      let+ tp = do_el code in
      D.Cut {tp; cut = hd, []}
    | `Reduce tag ->
      enact_rigid_coe line r s con tag
  end

and do_rigid_hcom code r s phi (bdy : D.con) =
  let open CM in
  CM.abort_if_inconsistent (ret D.tm_abort) @@
  begin
    dispatch_rigid_hcom code |>>
    function
    | `Done cut ->
      let tp = D.ElCut cut in
      let hd = D.UnstableCut (cut, D.KHCom (r, s, phi, bdy)) in
      ret @@ D.Cut {tp; cut = hd, []}
    | `Reduce tag ->
      enact_rigid_hcom code r s phi bdy tag
  end

and do_rigid_com (line : D.con) r s phi bdy =
  let open CM in
  let* code_s = do_ap line (D.dim_to_con s) in
  do_rigid_hcom code_s r s phi @<<
  splice_tm @@
  Splice.dim s @@ fun s ->
  Splice.con line @@ fun line ->
  Splice.con bdy @@ fun bdy ->
  Splice.term @@
  TB.lam @@ fun i ->
  TB.lam @@ fun prf ->
  TB.coe line i s @@
  TB.ap bdy [i; prf]

and do_rigid_mcoe lines r s fields =
  let open CM in
  let x = DimProbe.fresh () in
  let* linesx = inst_kan_tele_clo lines (D.DimProbe x) in
  enact_rigid_mcoe linesx x r s fields

and do_rigid_mcom tele r s phi bdys =
  let open CM in
  let D.Fields bdys = bdys in
  let x = DimProbe.fresh () in
  let rec go tele bdys =
    match (tele, bdys) with
    | D.KCell (lbl, code, tele), ((_, bdy) :: bdys) ->
      let* line = do_rigid_com (D.BindSym (x, code)) r (Dim.DimProbe x) phi bdy in
      let* tele = inst_kan_tele_clo tele line in
      let+ fields = go tele bdys in
      (lbl, D.LetSym (s, x, line)) :: fields
    | D.KEmpty, [] ->
      ret []
    | _, _ ->
      invalid_arg "bad do_rigid_mcom: telescope/field mismatch"
  in
  match tele, bdys with
  | D.KCell (lbl, code, tele), ((_, bdy) :: bdys) ->
    let* line = do_rigid_hcom code r (Dim.DimProbe x) phi bdy in
    let* tele = inst_kan_tele_clo tele line in
    let+ fields = go tele bdys in
    D.Fields ((lbl, D.LetSym (s, x, line)) :: fields)
  | D.KEmpty, [] ->
    ret @@ D.Fields []
  | _, _ ->
    invalid_arg "bad do_rigid_mcom: telescope/field mismatch"

and do_frm con =
  function
  | D.KAp (_, con') -> do_ap con con'
  | D.KFst -> do_fst con
  | D.KSnd -> do_snd con
  | D.KProj (lbl, ix) -> do_proj con lbl ix
  | D.KNatElim (mot, case_zero, case_suc) -> do_nat_elim mot case_zero case_suc con
  | D.KCircleElim (mot, case_base, case_loop) -> do_circle_elim mot case_base case_loop con
  | D.KElOut -> do_el_out con

and do_spine con =
  let open CM in
  function
  | [] -> ret con
  | k :: sp ->
    let* con' = do_frm con k in
    do_spine con' sp


and splice_tm t =
  let env, tm = Splice.compile t in
  CM.lift_ev env @@ eval tm

and splice_tp t =
  let env, tp = Splice.compile t in
  CM.lift_ev env @@ eval_tp tp

and splice_fields t =
  let env, fields = Splice.compile t in
  CM.lift_ev env @@ eval_fields fields
