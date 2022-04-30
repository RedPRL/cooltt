open Basis
open Monads

open CodeUnit

module S = Syntax
module D = Domain
module Sem = Semantics
module TB = TermBuilder

exception CCHM
exception CJHM
exception CFHM


module Error =
struct
  type t = IllTypedQuotationProblem of D.tp * D.con
  let pp fmt =
    function
    | IllTypedQuotationProblem (tp, con) ->
      Format.fprintf fmt "Ill-typed quotation problem %a : %a" D.pp_con con D.pp_tp tp
end

exception QuotationError of Error.t

open QuM
open Monad.Notation (QuM)
module MU = Monad.Util (QuM)
open Sem

let contractum_or x =
  function
  | `Done -> x
  | `Reduce y -> y

let guess_bound_name : D.con -> Ident.t =
  function
  | D.Lam (x, _) -> x
  | D.BindSym (_x, _) -> `Anon
  | D.Cut {tp = D.Pi (_, x, _); _} -> x
  | D.Cut {tp = D.TpSplit (_branch :: _); _} -> `Anon (* XXX what should we do here? *)
  | D.Split (_branch :: _) -> `Anon (* XXX what should we do here? *)
  | _ -> `Anon

let rec quote_con (tp : D.tp) con =
  QuM.abort_if_inconsistent (ret S.tm_abort) @@
  let* veil = read_veil in
  let* tp = contractum_or tp <@> lift_cmp @@ Sem.whnf_tp ~style:`UnfoldAll tp in
  let* con = contractum_or con <@> lift_cmp @@ Sem.whnf_con ~style:(`Veil veil) con in
  match tp, con with
  | _, D.Split branches ->
    let quote_branch (phi, clo) =
      lift_cmp @@ CmpM.test_sequent [phi] CofBuilder.bot |>> function
      | false ->
        let+ tphi = quote_cof phi
        and+ tbdy =
          bind_var (D.TpPrf phi) @@ fun prf ->
          let* body = lift_cmp @@ inst_tm_clo clo prf in
          quote_con tp body
        in
        Some (tphi, tbdy)
      | true ->
        ret None
    in
    let* tbranches = MU.filter_map quote_branch branches in
    ret @@ S.CofSplit tbranches

  | _, D.Cut {cut = (D.Var lvl, []); tp = TpDim} ->
    (* for dimension variables, check to see if we can prove them to be
        the same as 0 or 1 and return those instead if so. *)
    begin
      lift_cmp @@ CmpM.test_sequent [] @@ CofBuilder.eq0 (Dim.DimVar lvl) |>> function
      | true -> ret S.Dim0
      | false ->
        lift_cmp @@ CmpM.test_sequent [] @@ CofBuilder.eq1 (Dim.DimVar lvl) |>> function
        | true -> ret S.Dim1
        | false ->
          let+ ix = quote_var lvl in
          S.Var ix
    end

  | _, D.Cut {cut = (hd, sp); tp = _} ->
    quote_cut (hd, sp)

  | D.Pi (base, _, fam), D.Lam (ident, clo) ->
    quote_lam ~ident base @@ fun arg ->
    let* fib = lift_cmp @@ inst_tp_clo fam arg in
    let* ap = lift_cmp @@ inst_tm_clo clo arg in
    quote_con fib ap

  | D.Pi (base, ident, fam), con ->
    quote_lam ~ident base @@ fun arg ->
    let* fib = lift_cmp @@ inst_tp_clo fam arg in
    let* ap = lift_cmp @@ do_ap con arg in
    quote_con fib ap

  | D.Sg (base, _, fam), _ ->
    let* fst = lift_cmp @@ do_fst con in
    let* snd = lift_cmp @@ do_snd con in
    let* fib = lift_cmp @@ inst_tp_clo fam fst in
    let+ tfst = quote_con base fst
    and+ tsnd = quote_con fib snd in
    S.Pair (tfst, tsnd)

  | D.Signature sign, _ ->
    let+ tfields = quote_fields sign con in
    S.Struct tfields

  | D.Sub (tp, _phi, _clo), _ ->
    let+ tout =
      let* out = lift_cmp @@ do_sub_out con in
      quote_con tp out
    in
    S.SubIn tout

  | D.ElStable code, _ ->
    let* unfolded = lift_cmp @@ unfold_el code in
    quote_con unfolded con

  | _, D.Zero ->
    ret S.Zero

  | _, D.Suc n ->
    let+ tn = quote_con D.Nat n in
    S.Suc tn

  | _, D.Base ->
    ret S.Base

  | _, D.Loop r ->
    let+ tr = quote_dim r in
    S.Loop tr

  | D.TpDim, D.Dim0 ->
    ret @@ S.Dim0

  | D.TpDim, D.Dim1 ->
    ret @@ S.Dim1

  | D.TpCof, D.Cof cof ->
    let* cof = lift_cmp @@ cof_con_to_cof cof in
    quote_cof cof

  | D.TpPrf _, _ ->
    ret S.Prf

  | univ, D.StableCode code ->
    quote_stable_code univ code


  | D.Nat, D.FHCom (`Nat, r, s, phi, bdy) ->
    (* bdy : (i : 𝕀) (_ : [...]) → nat *)
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.con bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.ap bdy [i; prf]
    in
    quote_hcom (D.StableCode `Nat) r s phi bdy'

  | _univ, D.UnstableCode (`V (r, pcode, code, pequiv)) ->
    let+ tr, t_pcode, tcode, t_pequiv = quote_v_data r pcode code pequiv in
    S.CodeV (tr, t_pcode, tcode, t_pequiv)

  | _univ, D.UnstableCode (`HCom (r, s, phi, bdy)) ->
    (* bdy : (i : 𝕀) (_ : [...]) → nat *)
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.con bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.ap bdy [i; prf]
    in
    quote_hcom (D.StableCode `Univ) r s phi bdy'

  | D.Circle, D.FHCom (`Circle, r, s, phi, bdy) ->
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.con bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.ap bdy [i; prf]
    in
    quote_hcom (D.StableCode `Circle) r s phi bdy'

  | D.ElUnstable (`HCom (r,s,phi,bdy)), _ ->
    let+ tr = quote_dim r
    and+ ts = quote_dim s
    and+ tphi = quote_cof phi
    and+ tsides =
      quote_lam ~ident:`Anon (D.TpPrf phi) @@ fun _prf ->
      quote_con tp con
    and+ tcap =
      let* bdy_r = lift_cmp @@ do_ap2 bdy (D.dim_to_con r) D.Prf in
      let* el_bdy_r = lift_cmp @@ do_el bdy_r in
      quote_con el_bdy_r @<< lift_cmp @@ do_rigid_cap r s phi bdy con
    in
    S.Box (tr, ts, tphi, tsides, tcap)

  | D.ElUnstable (`V (r, pcode, code, pequiv)) as tp, _ ->
    begin
      lift_cmp (CmpM.test_sequent [] (CofBuilder.boundary r)) |>> function
      | true ->
        let branch phi : (S.t * S.t) m =
          let* tphi = quote_cof phi in
          bind_var (D.TpPrf phi) @@ fun _prf ->
          let+ tm = quote_con tp con in
          tphi, tm
        in
        let phis = [CofBuilder.eq0 r; CofBuilder.eq1 r] in
        let+ branches = MU.map branch phis in
        S.CofSplit branches
      | false ->
        let+ tr = quote_dim r
        and+ part =
          quote_lam ~ident:`Anon (D.TpPrf (CofBuilder.eq0 r)) @@ fun _ ->
          let* pcode_fib = lift_cmp @@ do_ap pcode D.Prf in
          let* tp = lift_cmp @@ do_el pcode_fib in
          quote_con tp con
        and+ tot =
          let* tp = lift_cmp @@ do_el code in
          let* proj = lift_cmp @@ do_rigid_vproj r pcode code pequiv con in
          quote_con tp proj
        and+ t_pequiv =
          let* tp_pequiv =
            lift_cmp @@ Sem.splice_tp @@
            Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
          in
          quote_con tp_pequiv pequiv
        in
        S.VIn (tr, t_pequiv, part, tot)
    end

  | _, D.LetSym (r, x, con) ->
    quote_con tp @<< lift_cmp @@ Sem.push_subst_con r x con

  | D.TpSplit branches as tp, _ ->
    let branch_body phi : S.t m =
      bind_var (D.TpPrf phi) @@ fun _prf ->
      quote_con tp con
    in
    let* branches =
      List.flatten <@>
      begin
        branches |> MU.map @@ fun (phi, clo) ->
        lift_cmp (CmpM.test_sequent [phi] CofBuilder.bot) |>> function
        | true ->
          ret []
        | false ->
          ret [phi,clo]
      end
    in
    begin
      match branches with
      | [_phi, tp_clo] ->
        let* tp = lift_cmp @@ inst_tp_clo tp_clo D.Prf in
        quote_con tp con
      | _ ->
        let phis = List.map fst branches in
        let+ tphis = MU.map quote_cof phis
        and+ tms = MU.map branch_body phis in
        S.CofSplit (List.combine tphis tms)
    end

  | D.TpLockedPrf phi, D.LockedPrfIn prf ->
    let+ prf = quote_con (D.TpPrf phi) prf in
    S.LockedPrfIn prf

  | _ ->
    Format.eprintf "bad: %a / %a@." D.pp_tp tp D.pp_con con;
    throw @@ QuotationError (Error.IllTypedQuotationProblem (tp, con))

and quote_fields (sign : D.sign) con : (Ident.user * S.t) list m =
  match sign with
  | D.Field (lbl, tp, sign_clo) ->
    let* fcon = lift_cmp @@ do_proj con lbl in
    let* sign = lift_cmp @@ inst_sign_clo sign_clo fcon in
    let* tfield = quote_con tp fcon in
    let+ tfields = quote_fields sign con in
    (lbl, tfield) :: tfields
  | D.Empty -> ret []

and quote_stable_field_code univ args (lbl, fam) =
  (* See [NOTE: Sig Code Quantifiers] for more details *)
  let rec go vars =
    function
    | [] -> quote_con univ @<< lift_cmp @@ do_aps fam vars
    | (ident, arg) :: args ->
      (* The 'do_aps' here instantiates the argument type families so that we can handle
         the telescopic nature of fields correctly. *)
      let* elarg = lift_cmp @@ CmpM.bind (do_aps arg vars) do_el in
      quote_lam ~ident elarg @@ fun var -> go (vars @ [var]) args
  in
  let+ tfam = go [] (args :> (Ident.t * D.con) list) in
  (lbl, tfam)

and quote_stable_code univ =
  function
  | `Nat ->
    ret S.CodeNat

  | `Circle ->
    ret S.CodeCircle

  | `Univ ->
    ret S.CodeUniv

  | `Pi (base, fam) ->
    let ident = guess_bound_name fam in
    let+ tbase = quote_con univ base
    and+ tfam =
      let* elbase = lift_cmp @@ do_el base in
      quote_lam ~ident elbase @@ fun var ->
      quote_con univ @<<
      lift_cmp @@ do_ap fam var
    in
    S.CodePi (tbase, tfam)

  | `Sg (base, fam) ->
    let ident = guess_bound_name fam in
    let+ tbase = quote_con univ base
    and+ tfam =
      let* elbase = lift_cmp @@ do_el base in
      quote_lam ~ident elbase @@ fun var ->
      quote_con univ @<<
      lift_cmp @@ do_ap fam var
    in
    S.CodeSg (tbase, tfam)
  | `Signature fields ->
    let+ tfields = MU.map_accum_left_m (quote_stable_field_code univ) fields
    in
    S.CodeSignature tfields

  | `Ext (n, code, `Global phi, bdry) ->
    let+ tphi =
      let* tp_cof_fam = lift_cmp @@ splice_tp @@ Splice.term @@ TB.cube n @@ fun _ -> TB.tp_cof in
      quote_global_con tp_cof_fam @@ `Global phi
    and+ tcode =
      let* tp_code = lift_cmp @@ splice_tp @@ Splice.term @@ TB.cube n @@ fun _ -> TB.univ in
      quote_con tp_code code
    and+ tbdry =
      let* tp_bdry =
        lift_cmp @@ splice_tp @@
        Splice.con code @@ fun code ->
        Splice.con phi @@ fun phi ->
        Splice.term @@
        TB.cube n @@ fun js ->
        TB.pi (TB.tp_prf @@ TB.ap phi js) @@ fun _ ->
        TB.el @@ TB.ap code js
      in
      quote_con tp_bdry bdry
    in
    S.CodeExt (n, tcode, tphi, tbdry)

and quote_global_con tp (`Global con) =
  globally @@
  let+ tm = quote_con tp con in
  `Global tm

and quote_lam ~ident tp mbdy =
  let+ bdy = bind_var tp mbdy in
  S.Lam (ident, bdy)

and quote_v_data r pcode code pequiv =
  let+ tr = quote_dim r
  and+ t_pcode = quote_con (D.Pi (D.TpPrf (CofBuilder.eq0 r), `Anon, D.const_tp_clo D.Univ)) pcode
  and+ tcode = quote_con D.Univ code
  and+ t_pequiv =
    let* tp_pequiv =
      lift_cmp @@ Sem.splice_tp @@
      Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
    in
    quote_con tp_pequiv pequiv
  in
  tr, t_pcode, tcode, t_pequiv


and quote_hcom code r s phi bdy =
  let* tcode = quote_con D.Univ code in
  let* tr = quote_dim r in
  let* ts = quote_dim s in
  let* tphi = quote_cof phi in
  let+ tbdy =
    let ident_i = guess_bound_name bdy in
    quote_lam ~ident:ident_i D.TpDim @@ fun i ->
    let* i_dim = lift_cmp @@ con_to_dim i in
    quote_lam ~ident:`Anon (D.TpPrf (CofBuilder.join [CofBuilder.eq r i_dim; phi])) @@ fun prf ->
    let* body = lift_cmp @@ do_ap2 bdy i prf in
    let* tp = lift_cmp @@ do_el code in
    quote_con tp body
  in
  S.HCom (tcode, tr, ts, tphi, tbdy)

and quote_tp_clo base fam =
  bind_var base @@ fun var ->
  let* tp = lift_cmp @@ inst_tp_clo fam var in
  quote_tp tp

and quote_sign : D.sign -> S.sign m =
  function
  | Field (ident, field, clo) ->
    let* tfield = quote_tp field in
    bind_var field @@ fun var ->
    let* fields = lift_cmp @@ inst_sign_clo clo var in
    let+ tfields = quote_sign fields in
    (ident, tfield) :: tfields
  | Empty -> ret []

and quote_tp (tp : D.tp) =
  let* veil = read_veil in
  let* tp = contractum_or tp <@> lift_cmp @@ Sem.whnf_tp ~style:(`Veil veil) tp in
  match tp with
  | D.Nat -> ret S.Nat
  | D.Circle -> ret S.Circle
  | D.Pi (base, ident, fam) ->
    let* tbase = quote_tp base in
    let+ tfam = quote_tp_clo base fam in
    S.Pi (tbase, ident, tfam)
  | D.Sg (base, ident, fam) ->
    let* tbase = quote_tp base in
    let+ tfam = quote_tp_clo base fam in
    S.Sg (tbase, ident, tfam)
  | D.Signature sign ->
    let+ sign = quote_sign sign in
    S.Signature sign
  | D.Univ ->
    ret S.Univ
  | D.ElStable code ->
    let+ tm = quote_stable_code D.Univ code in
    S.El tm
  | D.ElCut cut ->
    let+ tm = quote_cut cut in
    S.El tm
  | D.Sub (tp, phi, cl) ->
    let* ttp = quote_tp tp in
    let+ tphi = quote_cof phi
    and+ tm =
      bind_var (D.TpPrf phi) @@ fun prf ->
      let* body = lift_cmp @@ inst_tm_clo cl prf in
      quote_con tp body
    in
    S.Sub (ttp, tphi, tm)
  | D.TpDim ->
    ret S.TpDim
  | D.TpCof ->
    ret S.TpCof
  | D.TpPrf phi ->
    let+ tphi = quote_cof phi in
    S.TpPrf tphi
  | D.ElUnstable (`HCom (r, s, phi, bdy)) ->
    let+ tr = quote_dim r
    and+ ts = quote_dim s
    and+ tphi = quote_cof phi
    and+ tbdy =
      let* tp_bdy =
        lift_cmp @@
        Sem.splice_tp @@
        Splice.dim r @@ fun r ->
        Splice.cof phi @@ fun phi ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun _prf ->
        TB.univ
      in
      quote_con tp_bdy bdy
    in
    S.El (S.HCom (S.CodeUniv, tr, ts, tphi, tbdy))
  | D.ElUnstable (`V (r, pcode, code, pequiv)) ->
    let+ tr, t_pcode, tcode, t_pequiv = quote_v_data r pcode code pequiv in
    S.El (S.CodeV (tr, t_pcode, tcode, t_pequiv))
  | D.TpSplit branches ->
    let branch_body (phi, clo) : S.tp m =
      QuM.bind_var (D.TpPrf phi) @@ fun prf ->
      let* tp = lift_cmp @@ inst_tp_clo clo prf in
      quote_tp tp
    in
    let+ tphis = MU.map (fun (phi , _) -> quote_cof phi) branches
    and+ tps = MU.map branch_body branches in
    S.TpCofSplit (List.combine tphis tps)
  | D.TpLockedPrf phi ->
    let+ tphi = quote_cof phi in
    S.TpLockedPrf tphi

and quote_hd =
  function
  | D.Var lvl ->
    let+ i = quote_var lvl in
    S.Var i
  | D.Global sym ->
    ret @@ S.Global sym
  | D.Coe (code, r, s, con) ->
    let code_tp = D.Pi (D.TpDim, `Anon, D.const_tp_clo D.Univ) in
    let* tpcode = quote_con code_tp code in
    let* tr = quote_dim r in
    let* ts = quote_dim s in
    let* code_r = lift_cmp @@ do_ap code @@ D.dim_to_con r in
    let* tp_code_r = lift_cmp @@ do_el code_r in
    let+ tm = quote_con tp_code_r con in
    S.Coe (tpcode, tr, ts, tm)
  | D.UnstableCut (cut, ufrm) ->
    quote_unstable_cut cut ufrm

and quote_unstable_cut cut ufrm =
  match ufrm with
  | D.KHCom (r, s, phi, bdy) ->
    let code = D.Cut {cut; tp = D.Univ} in
    quote_hcom code r s phi bdy
  | D.KSubOut _ ->
    let+ tm = quote_cut cut in
    S.SubOut tm
  | D.KCap (r, s, phi, code) ->
    let* tr = quote_dim r in
    let* ts = quote_dim s in
    let* tphi = quote_cof phi in
    let* code_tp =
      lift_cmp @@
      Sem.splice_tp @@
      Splice.dim r @@ fun r ->
      Splice.cof phi @@ fun phi ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun _prf ->
      TB.univ
    in
    let+ tcode = quote_con code_tp code
    and+ tbox = quote_cut cut in
    S.Cap (tr, ts, tphi, tcode, tbox)
  | D.KVProj (r, pcode, code, pequiv) ->
    let* tr = quote_dim r in
    let* tpcode = quote_con (D.Pi (D.TpPrf (CofBuilder.eq0 r), `Anon, D.const_tp_clo D.Univ)) pcode in
    let* tcode = quote_con D.Univ code in
    let* t_pequiv =
      let* tp_pequiv =
        lift_cmp @@ Sem.splice_tp @@
        Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
      in
      quote_con tp_pequiv pequiv
    in
    let+ tv = quote_cut cut in
    S.VProj (tr, tpcode, tcode, t_pequiv, tv)
  | D.KLockedPrfUnlock (tp, phi, bdy) ->
    let+ tp = quote_tp tp
    and+ prf = quote_cut cut
    and+ cof = quote_cof phi
    and+ bdy =
      let bdy_tp = D.Pi (D.TpPrf phi, `Anon, D.const_tp_clo tp) in
      quote_con bdy_tp bdy
    in
    S.LockedPrfUnlock {tp; cof; prf; bdy}

and quote_dim d : S.t quote =
  quote_con D.TpDim @@
  D.dim_to_con d

and quote_cof phi =
  let module K = Kado.Syntax in
  let rec go =
    function
    | K.Var lvl ->
      let+ ix = quote_var lvl in
      S.Var ix
    | K.Cof phi ->
      match phi with
      | K.Eq (r, s) ->
        let+ tr = quote_dim r
        and+ ts = quote_dim s in
        S.CofBuilder.eq tr ts
      | K.Join phis ->
        let+ tphis = MU.map go phis in
        S.CofBuilder.join tphis
      | K.Meet phis ->
        let+ tphis = MU.map go phis in
        S.CofBuilder.meet tphis
  in
  go @<< lift_cmp @@ CmpM.simplify_cof phi

and quote_var lvl =
  let+ n = read_local in
  n - (lvl + 1)

and quote_cut (hd, spine) =
  let* tm = quote_hd hd in
  quote_spine tm spine

and quote_spine tm =
  function
  | [] -> ret tm
  | k :: spine ->
    let* tm' = quote_frm tm k in
    quote_spine tm' spine

and quote_frm tm =
  function
  | D.KNatElim (mot, zero_case, suc_case) ->
    let* mot_tp =
      lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.nat @@ fun _ -> TB.univ
    in
    let* tmot = quote_con mot_tp mot in
    let* tzero_case =
      let* mot_zero = lift_cmp @@ do_ap mot D.Zero in
      let* tp_mot_zero = lift_cmp @@ do_el mot_zero in
      quote_con tp_mot_zero zero_case
    in
    let* suc_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.con mot @@ fun mot ->
      Splice.term @@
      TB.pi TB.nat @@ fun x ->
      TB.pi (TB.el (TB.ap mot [x])) @@ fun _ih ->
      TB.el @@ TB.ap mot [TB.suc x]
    in
    let* tsuc_case = quote_con suc_tp suc_case in
    ret @@ S.NatElim (tmot, tzero_case, tsuc_case, tm)
  | D.KCircleElim (mot, base_case, loop_case) ->
    let* mot_tp =
      lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.circle @@ fun _ -> TB.univ
    in
    let* tmot = quote_con mot_tp mot in
    let* tbase_case =
      let* mot_base = lift_cmp @@ do_ap mot D.Base in
      let* tp_mot_base = lift_cmp @@ do_el mot_base in
      quote_con tp_mot_base base_case
    in
    let* loop_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.con mot @@ fun mot ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun x ->
      TB.el @@ TB.ap mot [TB.loop x]
    in
    let* tloop_case = quote_con loop_tp loop_case in
    ret @@ S.CircleElim (tmot, tbase_case, tloop_case, tm)
  | D.KFst ->
    ret @@ S.Fst tm
  | D.KSnd ->
    ret @@ S.Snd tm
  | D.KProj lbl ->
    ret @@ S.Proj (tm, lbl)
  | D.KAp (tp, con) ->
    let+ targ = quote_con tp con in
    S.Ap (tm, targ)
