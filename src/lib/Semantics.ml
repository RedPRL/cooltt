module S = Syntax
module D = Domain


exception Todo
exception CJHM
exception CFHM
exception CCHM

open CoolBasis
open Bwd

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
  match Bwd.nth env.conenv i with
  | v -> EvM.ret v
  | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

let get_local_tp i =
  let open EvM in
  let* env = EvM.read_local in
  match Bwd.nth env.tpenv i with
  | v -> EvM.ret v
  | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"


let tri_test_cof phi =
  let open CM in
  test_sequent [] phi |>>
  function
  | true -> CM.ret `True
  | false ->
    test_sequent [phi] Cof.bot |>>
    function
    | true -> ret `False
    | false -> ret `Indet

let rec normalize_cof phi =
  let open CM in
  match phi with
  | Cof.Cof (Cof.Eq _) | Cof.Var _ ->
    begin
      tri_test_cof phi |>>
      function
      | `True -> ret Cof.top
      | `False -> ret Cof.bot
      | `Indet -> ret phi
    end
  | Cof.Cof (Cof.Join phis) ->
    let+ phis = MU.map normalize_cof phis in
    Cof.join phis
  | Cof.Cof (Cof.Meet phis) ->
    let+ phis = MU.map normalize_cof phis in
    Cof.meet phis


module FaceLattice :
sig
  (** An atomic formula *)
  type atom = [`CofEq of D.dim * D.dim]

  (** A generator for a lattice homomorphism *)
  type gen = atom -> D.cof CM.m

  (** Extend a generator to a lattice homomorphism *)
  val extend : gen -> D.cof -> D.cof CM.m

  (** Quantifier elimination *)
  val forall : Symbol.t -> D.cof -> D.cof CM.m
end =
struct
  open CM

  type atom = [`CofEq of D.dim * D.dim]
  type gen = atom -> D.cof CM.m

  let extend gen =
    let rec loop =
      function
      | Cof.Var _ as phi -> ret phi
      | Cof.Cof phi ->
        match phi with
        | Cof.Join psis ->
          let+ psis = MU.map loop psis in
          Cof.Cof (Cof.Join psis)
        | Cof.Meet psis ->
          let+ psis = MU.map loop psis in
          Cof.Cof (Cof.Meet psis)
        | Cof.Eq (r, s) ->
          gen @@ `CofEq (r, s)
    in
    loop

  let forall sym =
    let i = D.DimProbe sym in
    extend @@
    function
    | `CofEq (r, s) ->
      test_sequent [] (Cof.eq r s) |>>
      function
      | true -> ret Cof.top
      | false ->
        test_sequent [] (Cof.eq i r) |>>
        function
        | true -> ret Cof.bot
        | false ->
          test_sequent [] (Cof.eq i s) |>>
          function
          | true -> ret Cof.bot
          | false -> ret @@ Cof.eq r s
end


let cap_boundary r s phi code box =
  Splice.foreign_dim r @@ fun r ->
  Splice.foreign_dim s @@ fun s ->
  Splice.foreign_cof phi @@ fun phi ->
  Splice.foreign code @@ fun code ->
  Splice.foreign box @@ fun box ->
  Splice.term @@
  TB.cof_split
    (TB.el @@ TB.ap code [s; TB.prf])
    [TB.eq r s, box;
     phi, TB.coe code s r box]

let v_boundary r pcode code =
  Splice.foreign_dim r @@ fun r ->
  Splice.foreign pcode @@ fun pcode ->
  Splice.foreign code @@ fun code ->
  Splice.term @@
  TB.cof_split TB.univ
    [TB.eq r TB.dim0, TB.ap pcode [TB.prf];
     TB.eq r TB.dim1, code]

let vproj_boundary r pcode code pequiv v =
  Splice.foreign_dim r @@ fun r ->
  Splice.foreign pcode @@ fun pcode ->
  Splice.foreign code @@ fun code ->
  Splice.foreign pequiv @@ fun pequiv ->
  Splice.foreign v @@ fun v ->
  Splice.term @@
  TB.cof_split
    (TB.el (TB.code_v r pcode code pequiv))
    [TB.eq r TB.dim0, TB.ap (TB.Equiv.equiv_fwd (TB.ap pequiv [TB.prf])) [v];
     TB.eq r TB.dim1, v]




let rec cof_con_to_cof : (D.con, D.con) Cof.cof_f -> D.cof CM.m =
  let open CM in
  function
  | Cof.Eq (r, s) ->
    let+ r = con_to_dim r
    and+ s = con_to_dim s in
    Cof.eq r s
  | Cof.Join phis ->
    let+ phis = MU.map con_to_cof phis in
    Cof.join phis
  | Cof.Meet phis ->
    let+ phis = MU.map con_to_cof phis in
    Cof.meet phis

and con_to_cof =
  let open CM in
  fun con ->
  whnf_inspect_con con |>>
  function
  | D.Cof cof -> cof_con_to_cof cof
  | D.Cut {cut = D.Var l, []} -> ret @@ Cof.var l
  | _ -> throw @@ NbeFailed "con_to_cof"

and con_to_dim =
  let open CM in
  fun con ->
  whnf_inspect_con con |>>
  function
  | D.DimCon0 -> ret D.Dim0
  | D.DimCon1 -> ret D.Dim1
  | D.Abort -> ret D.Dim0
  | D.Cut {cut = Var l, []} -> ret @@ D.DimVar l
  | D.Cut {cut = Global sym, []} -> ret @@ D.DimProbe sym
  | con ->
    Format.eprintf "bad: %a@." D.pp_con con;
    throw @@ NbeFailed "con_to_dim"


and subst_con : D.dim -> Symbol.t -> D.con -> D.con CM.m =
  fun r x con ->
  CM.ret @@ D.LetSym (r, x, con)

and push_subst_con : D.dim -> Symbol.t -> D.con -> D.con CM.m =
  fun r x ->
  let open CM in
  function
  | D.DimCon0 | D.DimCon1 | D.Prf | D.Zero | D.Abort | D.CodeNat | D.CodeUniv as con -> ret con
  | D.LetSym (s, y, con) ->
    push_subst_con r x @<< push_subst_con s y con
  | D.Suc con ->
    let+ con = subst_con r x con in
    D.Suc con
  | D.Lam (ident, clo) ->
    let+ clo = subst_clo r x clo in
    D.Lam (ident, clo)
  | BindSym (y, con) ->
    begin
      test_sequent [] (Cof.eq (D.DimProbe x) (D.DimProbe y)) |>>
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
  | D.CodePi (con0, con1) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1 in
    D.CodePi (con0, con1)
  | D.CodeSg (con0, con1) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1 in
    D.CodeSg (con0, con1)
  | D.CodePath (con0, con1) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1 in
    D.CodePath (con0, con1)
  | D.ElIn con ->
    let+ con = subst_con r x con in
    D.ElIn con
  | GoalRet con ->
    let+ con = subst_con r x con in
    D.GoalRet con
  | D.SubIn con ->
    let+ con = subst_con r x con in
    D.SubIn con
  | D.Cof (Cof.Join phis) ->
    let+ phis = MU.map (subst_con r x) phis in
    D.Cof (Cof.Join phis)
  | D.Cof (Cof.Meet phis) ->
    let+ phis = MU.map (subst_con r x) phis in
    D.Cof (Cof.Meet phis)
  | D.Cof (Cof.Eq (s, s')) ->
    let+ s = subst_con r x s
    and+ s' = subst_con r x s' in
    D.Cof (Cof.Eq (s, s'))
  | D.FHCom (tag, s, s', phi, bdy) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ bdy = subst_con r x bdy in
    D.FHCom (tag, s, s', phi, bdy)
  | D.Box (s, s', phi, sides, bdy) ->
    let+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ sides = subst_con r x sides
    and+ bdy = subst_con r x bdy in
    D.Box (s, s', phi, sides, bdy)
  | D.CodeV (s, pcode, code, pequiv) ->
    let+ s = subst_dim r x s
    and+ pcode = subst_con r x pcode
    and+ code = subst_con r x code
    and+ pequiv = subst_con r x pequiv in
    D.CodeV (s, pcode, code, pequiv)
  | D.VIn (s, equiv, pivot, base) ->
    let+ s = subst_dim r x s
    and+ equiv = subst_con r x equiv
    and+ pivot = subst_con r x pivot
    and+ base = subst_con r x base in
    D.VIn (s, equiv, pivot, base)
  | D.Cut {tp = D.TpDim; cut = (D.Global y, [])} as con ->
    begin
      test_sequent [] (Cof.eq (D.DimProbe x) (D.DimProbe y)) |>>
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

and subst_dim : D.dim -> Symbol.t -> D.dim -> D.dim CM.m =
  fun r x s ->
  let open CM in
  con_to_dim @<< push_subst_con r x @@ D.dim_to_con s

and subst_cof : D.dim -> Symbol.t -> D.cof -> D.cof CM.m =
  fun r x phi ->
  let open CM in
  con_to_cof @<< push_subst_con r x @@ D.cof_to_con phi

and subst_clo : D.dim -> Symbol.t -> D.tm_clo -> D.tm_clo CM.m =
  fun r x (Clo (tm, env)) ->
  let open CM in
  let+ env = subst_env r x env in
  D.Clo (tm, env)

and subst_tp_clo : D.dim -> Symbol.t -> D.tp_clo -> D.tp_clo CM.m =
  fun r x (TpClo (tp, env)) ->
  let open CM in
  let+ env = subst_env r x env in
  D.TpClo (tp, env)

and subst_env : D.dim -> Symbol.t -> D.env -> D.env CM.m =
  fun r x {tpenv; conenv} ->
  let open CM in
  let+ tpenv = MU.map_bwd (subst_tp r x) tpenv
  and+ conenv = MU.map_bwd (subst_con r x) conenv in
  D.{tpenv; conenv}

and subst_tp : D.dim -> Symbol.t -> D.tp -> D.tp CM.m =
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
  | D.Sub (base, phi, clo) ->
    let+ base = subst_tp r x base
    and+ phi = subst_cof r x phi
    and+ clo = subst_clo r x clo in
    D.Sub (base, phi, clo)
  | D.Univ | D.Nat | D.TpDim | D.TpCof | D.TpAbort as con -> ret con
  | D.TpPrf phi ->
    let+ phi = subst_cof r x phi in
    D.TpPrf phi
  | D.GoalTp (lbl, tp) ->
    let+ tp = subst_tp r x tp in
    D.GoalTp (lbl, tp)
  | D.El code ->
    let+ code = subst_con r x code in
    D.El code
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

and subst_cut : D.dim -> Symbol.t -> D.cut -> D.cut CM.m =
  fun r x (hd, sp) ->
  let open CM in
  let+ hd = subst_hd r x hd
  and+ sp = subst_sp r x sp in
  (hd, sp)

and subst_hd : D.dim -> Symbol.t -> D.hd -> D.hd CM.m =
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
  | D.HCom (code, s, s', phi, bdy) ->
    let+ code = subst_cut r x code
    and+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ bdy = subst_con r x bdy in
    D.HCom (code, s, s', phi, bdy)
  | D.Cap (s, s', phi, code, box) ->
    let+ code = subst_con r x code
    and+ s = subst_dim r x s
    and+ s' = subst_dim r x s'
    and+ phi = subst_cof r x phi
    and+ box = subst_cut r x box in
    D.Cap (s, s', phi, code, box)
  | D.VProj (s, pcode, code, pequiv, v) ->
    let+ s = subst_dim r x s
    and+ pcode = subst_con r x pcode
    and+ code = subst_con r x code
    and+ pequiv = subst_con r x pequiv
    and+ v = subst_cut r x v in
    D.VProj (s, pcode, code, pequiv, v)
  | D.SubOut (cut, phi, clo) ->
    let+ cut = subst_cut r x cut
    and+ phi = subst_cof r x phi
    and+ clo = subst_clo r x clo in
    D.SubOut (cut, phi, clo)
  | D.Split (tp, branches) ->
    let go_branch (phi, clo) =
      let+ phi = subst_cof r x phi
      and+ clo = subst_clo r x clo in
      (phi, clo)
    in
    let+ tp = subst_tp r x tp
    and+ branches = MU.map go_branch branches in
    D.Split (tp, branches)

and subst_frm : D.dim -> Symbol.t -> D.frm -> D.frm CM.m =
  fun r x ->
  let open CM in
  function
  | D.KFst | D.KSnd | D.KGoalProj | D.KElOut as frm -> ret frm
  | D.KAp (tp, arg) ->
    let+ tp = subst_tp r x tp
    and+ arg = subst_con r x arg in
    D.KAp (tp, arg)
  | D.KNatElim (con0, con1, con2) ->
    let+ con0 = subst_con r x con0
    and+ con1 = subst_con r x con1
    and+ con2 = subst_con r x con2 in
    D.KNatElim (con0, con1, con2)

and subst_sp : D.dim -> Symbol.t -> D.frm list -> D.frm list CM.m =
  fun r x ->
  CM.MU.map @@ subst_frm r x

and eval_tp : S.tp -> D.tp EvM.m =
  let open EvM in
  function
  | S.Nat -> ret D.Nat
  | S.Pi (base, ident, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Pi (vbase, ident, D.TpClo (fam, env))
  | S.Sg (base, ident, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Sg (vbase, ident, D.TpClo (fam, env))
  | S.Univ ->
    ret D.Univ
  | S.El tm ->
    let* con = eval tm in
    lift_cmp @@ do_el con
  | S.GoalTp (lbl, tp) ->
    let+ tp = eval_tp tp in
    D.GoalTp (lbl, tp)
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

and eval : S.t -> D.con EvM.m =
  let open EvM in
  fun tm ->
    match tm with
    | S.Var i ->
      let* con = get_local i in
      begin
        lift_cmp @@ whnf_con con |>> function
        | `Done -> ret con
        | `Reduce con -> ret con
      end
    | S.Global sym ->
      let* st = EvM.read_global in
      let* veil = EvM.read_veil in
      let tp, ocon = ElabState.get_global sym st in
      begin
        match ocon, Veil.policy sym veil with
        | Some con, `Transparent -> ret con
        | _ ->
          ret @@ D.Cut {tp; cut = (D.Global sym, [])}
      end
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
    | S.GoalRet tm ->
      let+ con = eval tm in
      D.GoalRet con
    | S.GoalProj tm ->
      let* con = eval tm in
      lift_cmp @@ do_goal_proj con
    | S.Coe (tpcode, tr, tr', tm) ->
      let* r = eval_dim tr in
      let* r' = eval_dim tr' in
      let* con = eval tm in
      begin
        CM.test_sequent [] (Cof.eq r r') |> lift_cmp |>> function
        | true ->
          ret con
        | false ->
          let* coe_abs = eval tpcode in
          lift_cmp @@ do_rigid_coe coe_abs r r' con
      end
    | S.HCom (tpcode, tr, ts, tphi, tm) ->
      let* r = eval_dim tr in
      let* s = eval_dim ts in
      let* phi = eval_cof tphi in
      let* vtpcode = eval tpcode in
      let* vbdy = eval tm in
      begin
        CM.test_sequent [] (Cof.join [Cof.eq r s; phi]) |> lift_cmp |>> function
        | true ->
          lift_cmp @@ do_ap2 vbdy (D.dim_to_con s) D.Prf
        | false ->
          lift_cmp @@ do_rigid_hcom vtpcode r s phi vbdy
      end
    | S.Com (tpcode, tr, ts, tphi, tm) ->
      let* r = eval_dim tr in
      let* s = eval_dim ts in
      let* phi = eval_cof tphi in
      begin
        CM.test_sequent [] (Cof.join [Cof.eq r s; phi]) |> lift_cmp |>> function
        | true ->
          append [D.dim_to_con s] @@ eval tm
        | false ->
          let* bdy = eval tm in
          let* vtpcode = eval tpcode in
          lift_cmp @@ do_rigid_com vtpcode r s phi bdy
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
    | S.Dim0 -> ret D.DimCon0
    | S.Dim1 -> ret D.DimCon1
    | S.Cof cof_f ->
      begin
        match cof_f with
        | Cof.Eq (tr, ts) ->
          let+ r = eval tr
          and+ s = eval ts in
          D.Cof (Cof.Eq (r, s))
        | Cof.Join tphis ->
          let+ phis = MU.map eval tphis in
          D.Cof (Cof.Join phis)
        | Cof.Meet tphis ->
          let+ phis = MU.map eval tphis in
          D.Cof (Cof.Meet phis)
      end
    | S.ForallCof tm ->
      let sym = Symbol.named "forall_probe" in
      let i = D.DimProbe sym in
      let* phi = append [D.dim_to_con i] @@ eval_cof tm in
      D.cof_to_con <@> lift_cmp @@ FaceLattice.forall sym phi
    | S.CofSplit (ttp, branches) ->
      let* tp = eval_tp ttp in
      let tphis, tms = List.split branches in
      let* phis = MU.map eval_cof tphis in
      let* con =
        let+ env = read_local in
        let pclos = List.map (fun tm -> D.Clo (tm, env)) tms in
        let hd = D.Split (tp, List.combine phis pclos) in
        D.Cut {tp; cut = hd, []}
      in
      begin
        lift_cmp @@ whnf_con con |>> function
        | `Done -> ret con
        | `Reduce con -> ret con
      end
    | S.CofAbort ->
      ret D.Abort
    | S.Prf ->
      ret D.Prf

    | S.CodePath (fam, bdry) ->
      let* vfam = eval fam in
      let* vbdry = eval bdry in
      ret @@ D.CodePath (vfam, vbdry)

    | S.CodePi (base, fam) ->
      let+ vbase = eval base
      and+ vfam = eval fam in
      D.CodePi (vbase, vfam)

    | S.CodeSg (base, fam) ->
      let+ vbase = eval base
      and+ vfam = eval fam in
      D.CodeSg (vbase, vfam)

    | S.CodeNat ->
      ret D.CodeNat

    | S.CodeUniv ->
      ret D.CodeUniv

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
      lift_cmp @@
      begin
        let open CM in
        CM.test_sequent [] (Cof.join [Cof.eq vr vs; vphi]) |>>
        function
        | true ->
          splice_tm @@ cap_boundary vr vs vphi vcode vbox
        | false ->
          do_rigid_cap vr vs vphi vcode vbox
      end

    | S.VIn (r, equiv, pivot, base) ->
      let+ vr = eval_dim r
      and+ vequiv = eval equiv
      and+ vpivot = eval pivot
      and+ vbase = eval base in
      D.VIn (vr, vequiv, vpivot, vbase)

    | S.VProj (r, pequiv, v) ->
      let* vr = eval_dim r in
      let* vv = eval v in
      begin
        CM.test_sequent [] (Cof.eq vr Dim0) |> lift_cmp |>> function
        | true -> (* r=0 *)
          let* vpequiv = eval pequiv in
          let* vequiv = lift_cmp @@ do_ap vpequiv D.Prf in
          lift_cmp @@ do_equiv_fwd vequiv vv
        | false ->
          CM.test_sequent [] (Cof.eq vr Dim1) |> lift_cmp |>> function
          | true -> (* r=1 *)
            ret vv
          | false ->
            lift_cmp @@ do_rigid_vproj vr vv
      end

    | S.CodeV (r, pcode, code, pequiv) ->
      let+ vr = eval_dim r
      and+ vpcode = eval pcode
      and+ vcode = eval code
      and+ vpequiv = eval pequiv in
      D.CodeV (vr, vpcode, vcode, vpequiv)

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
  | D.Lam _ | D.BindSym _ | D.Zero | D.Suc _ | D.Pair _ | D.GoalRet _ | D.Abort | D.SubIn _ | D.ElIn _
  | D.Cof _ | D.DimCon0 | D.DimCon1 | D.Prf
  | D.CodePath _ | CodePi _ | D.CodeSg _ | D.CodeNat | D.CodeUniv ->
    ret `Done
  | D.LetSym (r, x, con) ->
    reduce_to @<< push_subst_con r x con
  | D.Cut {cut} ->
    whnf_cut cut
  | D.FHCom (_, r, s, phi, bdy) ->
    begin
      test_sequent [] (Cof.join [Cof.eq r s; phi]) |>>
      function
      | true ->
        reduce_to @<< do_ap2 bdy (D.dim_to_con s) D.Prf
      | false ->
        ret `Done
    end
  | D.Box (r, s, phi, sides, cap) ->
    begin
      test_sequent [] (Cof.eq r s) |>>
      function
      | true ->
        reduce_to cap
      | false ->
        test_sequent [] phi |>>
        function
        | true ->
          reduce_to @<< do_ap sides D.Prf
        | false ->
          ret `Done
    end
  | D.CodeV (r, pcode, code, pequiv) ->
    begin
      test_sequent [] (Cof.boundary r) |>>
      function
      | true -> reduce_to @<< splice_tm @@ v_boundary r pcode code
      | false -> ret `Done
    end
  | D.VIn (r, pequiv, pivot, base) ->
    begin
      test_sequent [] (Cof.eq r Dim0) |>>
      function
      | true -> reduce_to @<< do_ap pivot D.Prf
      | false ->
        test_sequent [] (Cof.eq r Dim1) |>>
        function
        | true -> reduce_to base
        | false -> ret `Done
    end


and reduce_to con =
  let open CM in
  whnf_con con |>> function
  | `Done -> ret @@ `Reduce con
  | `Reduce con -> ret @@ `Reduce con

and plug_into sp con =
  let open CM in
  let* res = do_spine con sp in
  whnf_con res |>> function
  | `Done -> ret @@ `Reduce res
  | `Reduce res -> ret @@ `Reduce res

and whnf_hd hd =
  let open CM in
  match hd with
  | D.Global sym ->
    let* st = CM.read_global in
    begin
      match ElabState.get_global sym st with
      | tp, Some con ->
        reduce_to con
      | _, None | exception _ ->
        ret `Done
    end
  | D.Var _ -> ret `Done
  | D.Coe (abs, r, s, con) ->
    begin
      test_sequent [] (Cof.eq r s) |>> function
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
  | D.HCom (cut, r, s, phi, bdy) ->
    begin
      Cof.join [Cof.eq r s; phi] |> test_sequent [] |>> function
      | true ->
        reduce_to @<< do_ap2 bdy (D.dim_to_con s) D.Prf
      | false ->
        whnf_cut cut |>> function
        | `Done ->
          ret `Done
        | `Reduce code ->
          begin
            dispatch_rigid_hcom code |>>
            function
            | `Done _ ->
              ret `Done
            | `Reduce tag ->
              reduce_to @<< enact_rigid_hcom code r s phi bdy tag
          end
    end
  | D.SubOut (cut, phi, clo) ->
    begin
      test_sequent [] phi |>> function
      | true ->
        reduce_to @<< inst_tm_clo clo D.Prf
      | false ->
        whnf_cut cut |>> function
        | `Done ->
          ret `Done
        | `Reduce con ->
          reduce_to @<< do_sub_out con
    end
  | D.Split (tp, branches) ->
    let rec go =
      function
      | [] -> ret `Done
      | (phi, clo) :: branches ->
        test_sequent [] phi |>> function
        | true ->
          reduce_to @<< inst_tm_clo clo D.Prf
        | false ->
          go branches
    in
    go branches
  | D.Cap (r, s, phi, code, cut) ->
    begin
      test_sequent [] (Cof.join [Cof.eq r s; phi]) |>> function
      | true ->
        let box = D.Cut {cut; tp = D.ElUnstable (`HCom (r, s, phi, code))} in
        reduce_to @<< splice_tm @@ cap_boundary r s phi code box
      | false ->
        whnf_cut cut |>> function
        | `Done ->
          ret `Done
        | `Reduce box ->
          reduce_to @<< do_rigid_cap r s phi code box
    end
  | D.VProj (r, pcode, code, pequiv, cut) ->
    begin
      test_sequent [] (Cof.boundary r) |>>
      function
      | true ->
        let v = D.Cut {cut; tp = D.ElUnstable (`V (r, pcode, code, pequiv))} in
        reduce_to @<< splice_tm @@ vproj_boundary r pcode code pequiv v
      | false ->
        whnf_cut cut |>> function
        | `Done -> ret `Done
        | `Reduce v -> reduce_to @<< do_rigid_vproj r v
    end

and whnf_cut cut : D.con whnf CM.m =
  let open CM in
  let hd, sp = cut in
  whnf_hd hd |>>
  function
  | `Done -> ret `Done
  | `Reduce con -> plug_into sp con

and whnf_tp =
  let open CM in
  function
  | D.El con ->
    begin
      whnf_con con |>>
      function
      | `Done -> ret `Done
      | `Reduce con ->
        let+ tp = do_el con in
        `Reduce tp
    end
  | D.ElCut cut ->
    begin
      whnf_cut cut |>>
      function
      | `Done -> ret `Done
      | `Reduce con ->
        let+ tp = do_el con in
        `Reduce tp
    end
  | D.ElUnstable (`HCom (r, s, phi, bdy)) ->
    begin
      Cof.join [Cof.eq r s; phi] |> test_sequent [] |>>
      function
      | true ->
        let* tp  = do_el @<< do_ap2 bdy (D.dim_to_con s) D.Prf in
        begin
          whnf_tp tp |>>
          function
          | `Done -> ret @@ `Reduce tp
          | `Reduce tp -> ret @@ `Reduce tp
        end
      | false ->
        ret `Done
    end
  | tp ->
    ret `Done

and do_nat_elim (mot : D.con) zero (suc : D.con) n : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match n with
  | D.Zero ->
    ret zero
  | D.Suc n ->
    let* v = do_nat_elim mot zero suc n in
    do_ap2 suc n v
  | D.Cut {cut} ->
    let* fib = do_ap mot n in
    let+ elfib = do_el fib in
    cut_frm ~tp:elfib ~cut @@
    D.KNatElim (mot, zero, suc)
  | D.FHCom (`Nat, r, s, phi, bdy) ->
    (* bdy : (i : 𝕀) (_ : [_]) → nat *)
    splice_tm @@
    Splice.foreign mot @@ fun mot ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.foreign zero @@ fun zero ->
    Splice.foreign suc @@ fun suc ->
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
  | _ ->
    Format.eprintf "bad nat-elim: %a@." D.pp_con n;
    CM.throw @@ NbeFailed "Not a number"

and inst_tp_clo : D.tp_clo -> D.con -> D.tp CM.m =
  fun clo x ->
  match clo with
  | TpClo (bdy, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@
    eval_tp bdy

and inst_tm_clo : D.tm_clo -> D.con -> D.con CM.m =
  fun clo x ->
  match clo with
  | D.Clo (bdy, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@
    eval bdy

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


and do_goal_proj con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.GoalRet con -> ret con
    | D.Cut {tp = D.GoalTp (_, tp); cut} ->
      ret @@ cut_frm ~tp ~cut D.KGoalProj
    | _ ->
      CM.throw @@ NbeFailed "do_goal_proj"
  end

and do_fst con : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.Pair (con0, _) -> ret con0
    | D.Cut {tp = D.Sg (base, _, _); cut} ->
      ret @@ cut_frm ~tp:base ~cut D.KFst
    | _ ->
      throw @@ NbeFailed "Couldn't fst argument in do_fst"
  end

and do_snd con : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.Pair (_, con1) -> ret con1
    | D.Cut {tp = D.Sg (_, _, fam); cut} ->
      let* fst = do_fst con in
      let+ fib = inst_tp_clo fam fst in
      cut_frm ~tp:fib ~cut D.KSnd
    | _ ->
      throw @@ NbeFailed ("Couldn't snd argument in do_snd")
  end


and do_ap2 f a b =
  let open CM in
  let* fa = do_ap f a in
  do_ap fa b


and do_ap con arg =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.Lam (_, clo) ->
      inst_tm_clo clo arg

    | D.BindSym (x, con) ->
      let* r = con_to_dim arg in
      subst_con r x con

    | D.Cut {tp = D.Pi (base, _, fam); cut} ->
      let+ fib = inst_tp_clo fam arg in
      cut_frm ~tp:fib ~cut @@ D.KAp (base, arg)

    | con ->
      Format.eprintf "bad function: %a / %a@." D.pp_con con D.pp_con arg;
      throw @@ NbeFailed "Not a function in do_ap"
  end

and do_sub_out con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.SubIn con ->
      ret con
    | D.Cut {tp = D.Sub (tp, phi, clo); cut} ->
      ret @@ D.Cut {tp; cut = D.SubOut (cut, phi, clo), []}
    | _ ->
      throw @@ NbeFailed "do_sub_out"
  end

and do_rigid_cap r s phi code =
  let open CM in
  fun box ->
    abort_if_inconsistent D.Abort @@
    begin
      inspect_con box |>>
      function
      | D.Cut {cut} ->
        let* code_fib = do_ap2 code (D.dim_to_con r) D.Prf in
        let* tp = do_el code_fib in
        ret @@ D.Cut {tp; cut = D.Cap (r, s, phi, code, cut), []}
      | D.Box (_,_,_,_,cap) ->
        ret cap
      | _ ->
        throw @@ NbeFailed "do_rigid_cap"
    end

and do_rigid_vproj r v =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con v |>>
    function
    | D.Cut {tp = D.El vtp; cut} ->
      inspect_con vtp |>>
      begin
        function
        | D.CodeV (_,pcode,code,pequiv) ->
          let* tp = do_el code in
          ret @@ D.Cut {tp; cut = D.VProj (r, pcode, code, pequiv, cut), []}
        | _ ->
          throw @@ NbeFailed "do_rigid_vproj"
      end
    | D.VIn (_, _, _, base) ->
      ret base
    | _ ->
      throw @@ NbeFailed "do_rigid_vproj"
  end

and do_el_out con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.ElIn con ->
      ret con
    | D.Cut {tp = D.El con; cut} ->
      let+ tp = unfold_el con in
      cut_frm ~tp ~cut D.KElOut
    | D.Cut {tp; cut} ->
      Format.eprintf "bad: %a / %a@." D.pp_tp tp D.pp_con con;
      throw @@ NbeFailed "do_el_out"
    | _ ->
      Format.eprintf "bad el/out: %a@." D.pp_con con;
      throw @@ NbeFailed "do_el_out"
  end


and do_el : D.con -> D.tp CM.m =
  let open CM in
  fun con ->
    abort_if_inconsistent D.TpAbort @@
    begin
      inspect_con con |>>
      function
      | D.Cut {cut} ->
        ret @@ D.ElCut cut
      | D.FHCom (`Univ, r, s, phi, bdy) ->
        ret @@ D.ElUnstable (`HCom (r, s, phi, bdy))
      | D.CodeV (r, pcode, code, pequiv) ->
        ret @@ D.ElUnstable (`V (r, pcode, code, pequiv))
      | _ ->
        ret @@ D.El con
    end

and unfold_el : D.con -> D.tp CM.m =
  let open CM in
  fun con ->
    abort_if_inconsistent D.TpAbort @@
    begin
      inspect_con con |>>
      function

      | D.Cut {cut} ->
        CM.throw @@ NbeFailed "unfold_el on cut !!!"

      | D.CodeNat ->
        ret D.Nat

      | D.CodeUniv ->
        ret D.Univ

      | D.CodePi (base, fam) ->
        splice_tp @@
        Splice.foreign base @@ fun base ->
        Splice.foreign fam @@ fun fam ->
        Splice.term @@
        TB.pi (TB.el base) @@ fun x ->
        TB.el @@ TB.ap fam [x]

      | D.CodeSg (base, fam) ->
        splice_tp @@
        Splice.foreign base @@ fun base ->
        Splice.foreign fam @@ fun fam ->
        Splice.term @@
        TB.sg (TB.el base) @@ fun x ->
        TB.el @@ TB.ap fam [x]

      | D.CodePath (fam, bdry) ->
        splice_tp @@
        Splice.foreign fam @@ fun fam ->
        Splice.foreign bdry @@ fun bdry ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.sub (TB.el (TB.ap fam [i])) (TB.boundary i) @@ fun prf ->
        TB.ap bdry [i; prf]

      | con ->
        CM.throw @@ NbeFailed "unfold_el failed"
    end


and do_coe r s (abs : D.con) con =
  let open CM in
  test_sequent [] (Cof.eq r s) |>> function
  | true -> ret con
  | _ -> do_rigid_coe abs r s con


and dispatch_rigid_coe line =
  let open CM in
  let go x codex =
    match codex with
    | D.CodePi (basex, famx) ->
      `Reduce (`CoePi (x, basex, famx))
    | D.CodeSg (basex, famx) ->
      `Reduce (`CoeSg (x, basex, famx))
    | D.CodePath (famx, bdryx) ->
      `Reduce (`CoePath (x, famx, bdryx))
    | D.CodeNat ->
      `Reduce `CoeNat
    | D.CodeUniv ->
      `Reduce `CoeUniv
    | D.FHCom (`Univ, sx, s'x, phix, bdyx) ->
      `Reduce (`CoeHCom (x, sx, s'x, phix, bdyx))
    | D.CodeV (s, a, b, e) ->
      `Reduce (`V (x, s, a, b, e))
    | D.Cut {cut} ->
      `Done
    | _ ->
      `Unknown
  in
  let peek line =
    let x = Symbol.named "do_rigid_coe" in
    go x <@> whnf_inspect_con @<< do_ap line @@ D.dim_to_con @@ D.DimProbe x |>>
    function
    | `Reduce _ | `Done as res -> ret res
    | `Unknown ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_coe"
  in
  match line with
  | D.BindSym (x, codex) ->
    begin
      match go x codex with
      | `Reduce _ | `Done as res -> ret res
      | `Unknown -> peek line
    end
  | _ ->
    peek line

and dispatch_rigid_hcom code =
  let open CM in
  let go code =
    match code with
    | D.CodePi (base, fam) ->
      ret @@ `Reduce (`HComPi (base, fam))
    | D.CodeSg (base, fam) ->
      ret @@ `Reduce (`HComSg (base, fam))
    | D.CodePath (fam, bdry) ->
      ret @@ `Reduce (`HComPath (fam, bdry))
    | D.CodeNat ->
      ret @@ `Reduce (`FHCom `Nat)
    | D.CodeUniv ->
      ret @@ `Reduce (`FHCom `Univ)
    | D.FHCom (`Univ, r, s, phi, bdy) ->
      ret @@ `Reduce (`HComFHCom (r, s, phi, bdy))
    | D.CodeV (r, a, b, e) ->
      ret @@ `Reduce (`HComV (r, a, b, e))
    | D.Cut {cut} ->
      ret @@ `Done cut
    | _ ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_hcom"
  in
  go @<< whnf_inspect_con code

and enact_rigid_coe line r r' con tag =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match tag with
  | `CoeNat | `CoeUniv ->
    ret con
  | `CoePi (x, basex, famx) ->
    splice_tm @@
    Splice.foreign (D.BindSym (x, basex)) @@ fun base_line ->
    Splice.foreign (D.BindSym (x, famx)) @@ fun fam_line ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign con @@ fun bdy ->
    Splice.term @@ TB.Kan.coe_pi ~base_line ~fam_line ~r ~r' ~bdy
  | `CoeSg (x, basex, famx) ->
    splice_tm @@
    Splice.foreign (D.BindSym (x, basex)) @@ fun base_line ->
    Splice.foreign (D.BindSym (x, famx)) @@ fun fam_line ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign con @@ fun bdy ->
    Splice.term @@ TB.Kan.coe_sg ~base_line ~fam_line ~r ~r' ~bdy
  | `CoePath (x, famx, bdryx) ->
    splice_tm @@
    Splice.foreign (D.BindSym (x, famx)) @@ fun fam_line ->
    Splice.foreign (D.BindSym (x, bdryx)) @@ fun bdry_line ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign con @@ fun bdy ->
    Splice.term @@ TB.Kan.coe_path ~fam_line ~bdry_line ~r ~r' ~bdy
  | `CoeHCom (x, sx, s'x, phix, bdyx) ->
    splice_tm @@
    Splice.foreign (D.BindSym (x, D.dim_to_con sx)) @@ fun s ->
    Splice.foreign (D.BindSym (x, D.dim_to_con s'x)) @@ fun s' ->
    Splice.foreign (D.BindSym (x, D.cof_to_con phix)) @@ fun phi ->
    Splice.foreign (D.BindSym (x, bdyx)) @@ fun code ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign con @@ fun bdy ->
    let fhcom = TB.Kan.FHCom.{r = s; r' = s'; phi; bdy = code} in
    Splice.term @@ TB.Kan.FHCom.coe_fhcom ~fhcom ~r ~r' ~bdy
  | `V (x, s, pcode, code, pequiv) ->
    splice_tm @@
    Splice.foreign (D.BindSym (x, D.dim_to_con s)) @@ fun s ->
    Splice.foreign (D.BindSym (x, pcode)) @@ fun pcode ->
    Splice.foreign (D.BindSym (x, code)) @@ fun code ->
    Splice.foreign (D.BindSym (x, pequiv)) @@ fun pequiv ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign con @@ fun bdy ->
    let v = TB.Kan.V.{r = s; pcode; code; pequiv} in
    Splice.term @@ TB.Kan.V.coe_v ~v ~r ~r' ~bdy

and enact_rigid_hcom code r r' phi bdy tag =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match tag with
  | `HComPi (base, fam) ->
    splice_tm @@
    Splice.foreign base @@ fun base ->
    Splice.foreign fam @@ fun fam ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
    TB.Kan.hcom_pi ~base ~fam ~r ~r' ~phi ~bdy
  | `HComSg (base, fam) ->
    splice_tm @@
    Splice.foreign base @@ fun base ->
    Splice.foreign fam @@ fun fam ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
    TB.Kan.hcom_sg ~base ~fam ~r ~r' ~phi ~bdy
  | `HComPath (fam, bdry) ->
    splice_tm @@
    Splice.foreign fam @@ fun fam ->
    Splice.foreign bdry @@ fun bdry ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
    TB.Kan.hcom_path ~fam ~bdry ~r ~r' ~phi ~bdy
  | `FHCom tag ->
    (* bdy : (i : 𝕀) (_ : [...]) → el(<nat>) *)
    let+ bdy' =
      splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_out @@ TB.ap bdy [i; prf]
    in
    D.ElIn (D.FHCom (tag, r, r', phi, bdy'))
  | `HComFHCom (h_r,h_r',h_phi,h_bdy) ->
    splice_tm @@
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.foreign_dim h_r @@ fun h_r ->
    Splice.foreign_dim h_r' @@ fun h_r' ->
    Splice.foreign_cof h_phi @@ fun h_phi ->
    Splice.foreign h_bdy @@ fun h_bdy ->
    Splice.term @@
    let fhcom = TB.Kan.FHCom.{r = h_r; r' = h_r'; phi = h_phi; bdy = h_bdy} in
    TB.Kan.FHCom.hcom_fhcom ~fhcom ~r ~r' ~phi ~bdy
  | `HComV (h_r,h_pcode,h_code,h_pequiv) ->
    splice_tm @@
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim r' @@ fun r' ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.foreign_dim h_r @@ fun h_r ->
    Splice.foreign h_pcode @@ fun h_pcode ->
    Splice.foreign h_code @@ fun h_code ->
    Splice.foreign h_pequiv @@ fun h_pequiv ->
    Splice.term @@
    let v = TB.Kan.V.{r = h_r; pcode = h_pcode; code = h_code; pequiv = h_pequiv} in
    TB.Kan.V.hcom_v ~v ~r ~r' ~phi ~bdy
  | `Done cut ->
    let tp = D.ElCut cut in
    let hd = D.HCom (cut, r, r', phi, bdy) in
    ret @@ D.Cut {tp; cut = hd, []}

and do_rigid_coe (line : D.con) r s con =
  let open CM in
  CM.abort_if_inconsistent D.Abort @@
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
  CM.abort_if_inconsistent D.Abort @@
  begin
    dispatch_rigid_hcom code |>>
    function
    | `Done cut ->
      let tp = D.ElCut cut in
      let hd = D.HCom (cut, r, s, phi, bdy) in
      ret @@ D.Cut {tp; cut = hd, []}
    | `Reduce tag ->
      enact_rigid_hcom code r s phi bdy tag
  end

and do_rigid_com (line : D.con) r s phi bdy =
  let open CM in
  let* code_s = do_ap line (D.dim_to_con s) in
  do_rigid_hcom code_s r s phi @<<
  splice_tm @@
  Splice.foreign_dim s @@ fun s ->
  Splice.foreign line @@ fun line ->
  Splice.foreign bdy @@ fun bdy ->
  Splice.term @@
  TB.lam @@ fun i ->
  TB.lam @@ fun prf ->
  TB.coe line i s @@
  TB.ap bdy [i; prf]

and do_frm con =
  function
  | D.KAp (_, con') -> do_ap con con'
  | D.KFst -> do_fst con
  | D.KSnd -> do_snd con
  | D.KNatElim (mot, case_zero, case_suc) -> do_nat_elim mot case_zero case_suc con
  | D.KGoalProj -> do_goal_proj con
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

and do_equiv_fwd e a =
  let open CM in
  let* f = do_el_out e |>> do_fst |>> do_el_out in
  do_ap f a
