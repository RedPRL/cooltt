open Basis
open Cubical
open Bwd

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


type whnf_style = [`UnfoldNone | `UnfoldAll | `Veil of Veil.t]


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
  val forall : DimProbe.t -> D.cof -> D.cof CM.m
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
    let i = Dim.DimProbe sym in
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
    whnf_inspect_con ~style:`UnfoldAll con |>>
    function
    | D.Cof cof -> cof_con_to_cof cof
    | D.Cut {cut = D.Var l, []; _} -> ret @@ Cof.var l
    | _ -> throw @@ NbeFailed "con_to_cof"

and con_to_dim =
  let open CM in
  fun con ->
    whnf_inspect_con ~style:`UnfoldAll con |>>
    function
    | D.Dim0 -> ret Dim.Dim0
    | D.Dim1 -> ret Dim.Dim1
    | D.DimProbe x -> ret @@ Dim.DimProbe x
    | D.Cut {cut = Var l, []; _} -> ret @@ Dim.DimVar l
    | con ->
      Format.eprintf "bad: %a@." D.pp_con con;
      throw @@ NbeFailed "con_to_dim"


and subst_con : D.dim -> DimProbe.t -> D.con -> D.con CM.m =
  fun r x con ->
  CM.ret @@ D.LetSym (r, x, con)

and push_subst_con : D.dim -> DimProbe.t -> D.con -> D.con CM.m =
  fun r x ->
  let open CM in
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
      test_sequent [] (Cof.eq (Dim.DimProbe x) (Dim.DimProbe y)) |>>
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
    let+ fields = MU.map (MU.second (subst_con r x)) fields in
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
      test_sequent [] (Cof.eq (Dim.DimProbe x) (Dim.DimProbe y)) |>>
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
  | D.LockedPrfIn prf ->
    let+ prf = subst_con r x prf in
    D.LockedPrfIn prf

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

and subst_sign_clo : D.dim -> DimProbe.t -> D.sign_clo -> D.sign_clo CM.m =
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

and subst_sign : D.dim -> DimProbe.t -> D.sign -> D.sign CM.m =
  fun r x ->
  let open CM in
  function
  | D.Field (ident, tp, clo) ->
    let+ tp = subst_tp r x tp
    and+ clo = subst_sign_clo r x clo in
    D.Field (ident, tp, clo)
  | D.Empty -> ret D.Empty

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
  | D.Signature sign ->
    let+ sign = subst_sign r x sign in
    D.Signature sign
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
  | D.TpLockedPrf phi ->
    let+ phi = subst_cof r x phi in
    D.TpLockedPrf phi

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
  | `Signature fields ->
    let+ fields = MU.map (MU.second (subst_con r x)) fields in
    `Signature fields
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
  | D.KLockedPrfUnlock (tp, phi, con) ->
    let+ tp = subst_tp r x tp
    and+ phi = subst_cof r x phi
    and+ con = subst_con r x con in
    D.KLockedPrfUnlock (tp, phi, con)


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

and eval_sign : S.sign -> D.sign EvM.m =
  let open EvM in
  function
  | [] -> ret D.Empty
  | (ident, field) :: fields ->
    let+ env = read_local
    and+ vfield = eval_tp field in
    D.Field (ident, vfield, D.Clo (fields, env))

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
    let+ vsign = eval_sign sign in
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
  | S.TpLockedPrf phi ->
    let+ phi = eval_cof phi in
    D.TpLockedPrf phi

and eval : S.t -> D.con EvM.m =
  let open EvM in
  fun tm ->
    match tm with
    | S.Var i ->
      let* con = get_local i in
      lift_cmp @@ whnf_inspect_con ~style:`UnfoldNone con
    | S.Global sym ->
      let* st = EvM.read_global in
      let tp, _ = RefineState.get_global sym st in
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
        CM.test_sequent [] (Cof.boundary ~dim0:Dim.Dim0 ~dim1:Dim.Dim1 r) |> lift_cmp |>> function
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
      let+ vfields = MU.map (MU.second eval) fields in
      D.Struct vfields
    | S.Proj (t, lbl) ->
      let* con = eval t in
      lift_cmp @@ do_proj con lbl
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
          lift_cmp @@ do_rigid_coe ~style:`UnfoldNone coe_abs r r' con
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
          lift_cmp @@ do_rigid_hcom ~style:`UnfoldNone vtpcode r r' phi bdy
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
      let sym = DimProbe.fresh () in
      let i = Dim.DimProbe sym in
      let* phi = append [D.dim_to_con i] @@ eval_cof tm in
      D.cof_to_con <@> lift_cmp @@ FaceLattice.forall sym phi
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
    | S.CodeSignature fields ->
      let+ vfields = fields |> MU.map @@ fun (ident, tp) ->
        let+ vtp = eval tp in
        (ident, vtp)
      in
      D.StableCode (`Signature vfields)
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

    | S.LockedPrfIn prf ->
      let+ prf = eval prf in
      D.LockedPrfIn prf

    | S.LockedPrfUnlock {tp; cof; prf; bdy} ->
      let* tp = eval_tp tp in
      let* cof = eval_cof cof in
      let* prf = eval prf in
      let* bdy = eval bdy in
      lift_cmp @@ do_prf_unlock tp cof prf bdy

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


and whnf_con ~style : D.con -> D.con whnf CM.m =
  let open CM in
  function
  | D.Lam _ | D.BindSym _ | D.Zero | D.Suc _ | D.Base | D.Pair _ | D.Struct _ | D.SubIn _ | D.ElIn _ | D.LockedPrfIn _
  | D.Cof _ | D.Dim0 | D.Dim1 | D.Prf | D.StableCode _ | D.DimProbe _ ->
    ret `Done
  | D.LetSym (r, x, con) ->
    reduce_to ~style @<< push_subst_con r x con
  | D.Cut {cut; _} ->
    whnf_cut ~style cut
  | D.FHCom (_, r, r', phi, bdy) ->
    whnf_boundary ~style @@ Splice.Bdry.hcom ~r ~r' ~phi ~bdy
  | D.Box (r, r', phi, sides, cap) ->
    whnf_boundary ~style @@ Splice.Bdry.box ~r ~r' ~phi ~sides ~cap
  | D.UnstableCode code ->
    whnf_boundary ~style @@ Splice.Bdry.unstable_code code
  | D.VIn (r, _pequiv, pivot, base) ->
    whnf_boundary ~style @@ Splice.Bdry.vin ~r ~pivot ~base
  | D.Loop r ->
    begin
      test_sequent [] (Cof.boundary ~dim0:Dim.Dim0 ~dim1:Dim.Dim1 r) |>>
      function
      | true -> ret (`Reduce D.Base)
      | false -> ret `Done
    end
  | D.Split branches ->
    let rec go =
      function
      | [] -> ret `Done
      | (phi, clo) :: branches ->
        test_sequent [] phi |>> function
        | true ->
          reduce_to ~style @<< inst_tm_clo clo D.Prf
        | false ->
          go branches
    in
    go branches

and whnf_boundary ~style (psi, bdry) =
  let open CM in
  test_sequent [] psi |>>
  function
  | true -> reduce_to ~style @<< splice_tm bdry
  | false -> ret `Done

and reduce_to ~style con =
  let open CM in
  whnf_con ~style con |>> function
  | `Done -> ret @@ `Reduce con
  | `Reduce con -> ret @@ `Reduce con

and reduce_to_tp ~style tp =
  let open CM in
  whnf_tp ~style tp |>> function
  | `Done -> ret @@ `Reduce tp
  | `Reduce tp -> ret @@ `Reduce tp


and plug_into ~style sp con =
  let open CM in
  let* res = do_spine con sp in
  whnf_con ~style res |>> function
  | `Done -> ret @@ `Reduce res
  | `Reduce res -> ret @@ `Reduce res

and should_unfold_symbol style sym =
  match style with
  | `UnfoldNone ->
    false
  | `UnfoldAll -> true
  | `Veil veil ->
    match Veil.policy sym veil with
    | `Transparent -> true
    | `Translucent -> false

and whnf_hd ~style hd =
  let open CM in
  match hd with
  | D.Global sym ->
    if should_unfold_symbol style sym then
      let* st = CM.read_global in
      begin
        match RefineState.get_global sym st with
        | _tp, Some con ->
          reduce_to ~style con
        | _, None | exception _ ->
          ret `Done
      end
    else
      ret `Done
  | D.Var _ -> ret `Done
  | D.Coe (abs, r, s, con) ->
    begin
      test_sequent [] (Cof.eq r s) |>> function
      | true -> reduce_to ~style con
      | false ->
        begin
          dispatch_rigid_coe ~style abs |>>
          function
          | `Done ->
            ret `Done
          | `Reduce tag ->
            reduce_to ~style @<< enact_rigid_coe abs r s con tag
        end
    end
  | D.UnstableCut (cut, ufrm) ->
    let phi, bdry = Splice.Bdry.unstable_frm cut ufrm in
    test_sequent [] phi |>>
    function
    | true ->
      reduce_to ~style @<< splice_tm bdry
    | false ->
      whnf_cut ~style cut |>>
      function
      | `Done ->
        ret `Done
      | `Reduce con ->
        reduce_to ~style @<< do_rigid_unstable_frm ~style con ufrm

and do_rigid_unstable_frm ~style con ufrm =
  match ufrm with
  | D.KHCom (r, s, phi, bdy) ->
    do_rigid_hcom ~style con r s phi bdy
  | D.KCap (r, s, phi, code) ->
    do_rigid_cap r s phi code con
  | D.KVProj (r, pcode, code, pequiv) ->
    do_rigid_vproj r pcode code pequiv con
  | D.KSubOut _ ->
    do_sub_out con
  | D.KLockedPrfUnlock (tp, phi, bdy) ->
    do_prf_unlock tp phi con bdy

and whnf_cut ~style : D.cut -> D.con whnf CM.m =
  let open CM in
  fun (hd, sp) ->
    whnf_hd ~style hd |>>
    function
    | `Done -> ret `Done
    | `Reduce con -> plug_into ~style sp con

and whnf_tp ~style =
  let open CM in
  function
  | D.ElCut cut ->
    begin
      whnf_cut ~style cut |>>
      function
      | `Done ->
        ret `Done
      | `Reduce con ->
        reduce_to_tp ~style @<< do_el con
    end
  | D.ElUnstable code ->
    let phi, bdry = Splice.Bdry.unstable_code code in
    begin
      test_sequent [] phi |>> function
      | true -> reduce_to_tp ~style @<< do_el @<< splice_tm bdry
      | false -> ret `Done
    end
  | D.TpSplit branches ->
    let rec go =
      function
      | [] -> ret `Done
      | (phi, tp_clo) :: branches ->
        test_sequent [] phi |>> function
        | true ->
          reduce_to_tp ~style @<< inst_tp_clo tp_clo D.Prf
        | false ->
          go branches
    in
    go branches
  | _tp ->
    ret `Done

and whnf_tp_ ~style tp =
  let open CM in
  whnf_tp ~style tp |>>
  function
  | `Done -> ret tp
  | `Reduce tp -> ret tp

and whnf_con_ ~style con =
  let open CM in
  whnf_con ~style con |>>
  function
  | `Done -> ret con
  | `Reduce con -> ret con

and do_nat_elim (mot : D.con) zero (suc : D.con) : D.con -> D.con CM.m =
  let open CM in

  let rec go con =
    whnf_inspect_con ~style:`UnfoldNone con |>>
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
  whnf_inspect_con ~style:`UnfoldNone c |>>
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

and inst_sign_clo : D.sign_clo -> D.con -> D.sign CM.m =
  fun clo x ->
  match clo with
  | D.Clo (sign, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@ eval_sign sign

(* reduces a constructor to something that is stable to pattern match on *)
and whnf_inspect_con ~style con =
  let open CM in
  whnf_con ~style con |>>
  function
  | `Done -> ret con
  | `Reduce con' -> ret con'

(* reduces a constructor to something that is stable to pattern match on,
 * _including_ type annotations on cuts *)
and inspect_con ~style con =
  let open CM in
  whnf_inspect_con ~style con |>>
  function
  | D.Cut {tp; cut} as con ->
    begin
      whnf_tp ~style:`UnfoldAll tp |>>
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
    inspect_con ~style:`UnfoldNone con |>>
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
    inspect_con ~style:`UnfoldNone con |>>
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

and cut_frm_sign (cut : D.cut) (sign : D.sign) (lbl : Ident.user) =
  let open CM in
  match sign with
  | D.Field (flbl, tp, _) when Ident.equal flbl lbl -> ret @@ cut_frm ~tp ~cut (D.KProj lbl)
  | D.Field (flbl, _, clo) ->
    (* FIXME: Is this right?? *)
    let* field = cut_frm_sign cut sign flbl in
    let* sign = inst_sign_clo clo field in
    cut_frm_sign cut sign lbl
  | D.Empty ->
    throw @@ NbeFailed ("Couldn't find field label in cut_frm_sign")

and do_proj (con : D.con) (lbl : Ident.user) : D.con CM.m =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis = splice_tm @@ Splice.Macro.commute_split con phis (fun tm -> TB.proj tm lbl) in
  begin
    inspect_con ~style:`UnfoldNone con |>>
    function
    | D.Struct fields ->
      begin
        match List.assoc_opt lbl fields with
        | Some con -> ret con
        | None -> throw @@ NbeFailed "Couldn't proj argument in do_proj, struct was missing field"
      end
    | D.Split branches ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.Signature sign; cut} ->
      cut_frm_sign cut sign lbl
    | _ ->
      throw @@ NbeFailed ("Couldn't proj argument in do_proj")
  end

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
    inspect_con ~style:`UnfoldNone con |>>
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
    inspect_con ~style:`UnfoldNone con |>>
    function
    | D.SubIn con ->
      ret con
    | D.Cut {tp = D.Sub (tp, phi, clo); cut} ->
      ret @@ D.Cut {tp; cut = D.UnstableCut (cut, D.KSubOut (phi, clo)), []}
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | _ ->
      throw @@ NbeFailed "do_sub_out"
  end

and do_prf_unlock tp phi con bdy =
  let open CM in
  abort_if_inconsistent (ret D.tm_abort) @@
  let splitter con phis =
    splice_tm @@
    Splice.con bdy @@ fun bdy ->
    Splice.cof phi @@ fun phi ->
    Splice.tp tp @@ fun tp ->
    Splice.Macro.commute_split con phis @@ fun prf ->
    TB.locked_prf_unlock tp ~cof:phi ~prf ~bdy
  in
  begin
    inspect_con ~style:`UnfoldNone con |>>
    function
    | D.LockedPrfIn con ->
      do_ap bdy con
    | D.Cut {tp = D.TpLockedPrf phi; cut} ->
      ret @@ D.Cut {tp; cut = D.UnstableCut (cut, D.KLockedPrfUnlock (tp, phi, bdy)), []}
    | D.Split branches as con ->
      splitter con @@ List.map fst branches
    | D.Cut {tp = D.TpSplit branches; _} as con ->
      splitter con @@ List.map fst branches
    | _ ->
      throw @@ NbeFailed "do_prf_unlock"
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
    inspect_con ~style:`UnfoldNone box |>>
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
    inspect_con ~style:`UnfoldNone v |>>
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
    inspect_con ~style:`UnfoldNone con |>>
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
      inspect_con ~style:`UnfoldNone con |>>
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
      | `Signature fields ->
        let (lbls, field_cons) = ListUtil.unzip fields in
        splice_tp @@
        Splice.cons field_cons @@ fun fields ->
        Splice.term @@ TB.signature @@ List.map2 (fun ident fam -> (ident, fun args -> TB.el @@ TB.ap fam args)) lbls fields

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


and dispatch_rigid_coe ~style line =
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
        FaceLattice.forall x phix
      in
      ret @@ `Reduce (`Split phis)
    | D.Cut _ ->
      ret @@ `Done
    | _ ->
      ret @@ `Unknown
  in
  let peek line =
    let x = DimProbe.fresh () in
    go x @<< whnf_inspect_con ~style @<< do_ap line @@ D.dim_to_con @@ Dim.DimProbe x |>>
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

and dispatch_rigid_hcom ~style code =
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
  go @<< whnf_inspect_con ~style code

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
      | `Signature fields ->
        let (lbls, fams) = ListUtil.unzip fields in
        splice_tm @@
        Splice.cons (List.map (fun famx -> D.BindSym (x, famx)) fams) @@ fun fam_lines ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.con con @@ fun bdy ->
        Splice.term @@ TB.Kan.coe_sign ~field_lines:(ListUtil.zip lbls fam_lines) ~r ~r' ~bdy
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
      | `Signature fields ->
        let (lbls, fams) = ListUtil.unzip fields in
        splice_tm @@
        Splice.cons fams @@ fun fams ->
        Splice.dim r @@ fun r ->
        Splice.dim r' @@ fun r' ->
        Splice.cof phi @@ fun phi ->
        Splice.con bdy @@ fun bdy ->
        Splice.term @@
        TB.Kan.hcom_sign ~fields:(ListUtil.zip lbls fams) ~r ~r' ~phi ~bdy
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

and do_rigid_coe ~style (line : D.con) r s con =
  let open CM in
  CM.abort_if_inconsistent (ret D.tm_abort) @@
  begin
    dispatch_rigid_coe ~style line |>>
    function
    | `Done ->
      let hd = D.Coe (line, r, s, con) in
      let* code = do_ap line (D.dim_to_con s) in
      let+ tp = do_el code in
      D.Cut {tp; cut = hd, []}
    | `Reduce tag ->
      enact_rigid_coe line r s con tag
  end

and do_rigid_hcom ~style code r s phi (bdy : D.con) =
  let open CM in
  CM.abort_if_inconsistent (ret D.tm_abort) @@
  begin
    dispatch_rigid_hcom ~style code |>>
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
  do_rigid_hcom ~style:`UnfoldAll code_s r s phi @<<
  splice_tm @@
  Splice.dim s @@ fun s ->
  Splice.con line @@ fun line ->
  Splice.con bdy @@ fun bdy ->
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
  | D.KProj lbl -> do_proj con lbl
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
