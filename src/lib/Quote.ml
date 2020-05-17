module S = Syntax
module D = Domain
module Sem = Semantics
module TB = TermBuilder

exception Todo
exception CCHM
exception CJHM
exception CFHM

open CoolBasis
open Monads

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

module QTB :
sig
  val lam : ?ident:Ident.t -> D.tp -> (D.con -> S.t m) -> S.t m
end =
struct
  let lam ?(ident = `Anon) tp mbdy =
    bind_var ~abort:S.CofAbort tp @@ fun arg ->
    let+ bdy = mbdy arg in
    S.Lam (ident, bdy)
end

let contractum_or x =
  function
  | `Done -> x
  | `Reduce y -> y


let rec quote_con (tp : D.tp) con : S.t m =
  QuM.abort_if_inconsistent S.CofAbort @@
  let* tp = contractum_or tp <@> lift_cmp @@ Sem.whnf_tp tp in
  match tp, con with
  | _, D.Abort -> ret S.CofAbort
  | _, D.Cut {cut = (D.Var lvl, []); tp = TpDim} ->
    (* for dimension variables, check to see if we can prove them to be
        the same as 0 or 1 and return those instead if so. *)
    begin
      lift_cmp @@ CmpM.test_sequent [] @@ Cof.eq (D.DimVar lvl) D.Dim0 |>> function
      | true -> ret S.Dim0
      | false ->
        lift_cmp @@ CmpM.test_sequent [] @@ Cof.eq (D.DimVar lvl) D.Dim1 |>> function
        | true -> ret S.Dim1
        | false ->
          let+ ix = quote_var lvl in
          S.Var ix
    end

  | _, D.Cut {cut = (hd, sp); tp} ->
    quote_cut (hd, sp)

  | D.Pi (base, _, fam), D.Lam (ident, clo) ->
    QTB.lam ~ident base @@ fun arg ->
    let* fib = lift_cmp @@ inst_tp_clo fam arg in
    let* ap = lift_cmp @@ inst_tm_clo clo arg in
    quote_con fib ap

  | D.Pi (base, ident, fam), con ->
    QTB.lam ~ident base @@ fun arg ->
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

  | D.Sub (tp, phi, clo), _ ->
    let+ tout =
      let* out = lift_cmp @@ do_sub_out con in
      quote_con tp out
    in
    S.SubIn tout

  | D.El code, _ ->
    let+ tout =
      let* unfolded = lift_cmp @@ unfold_el code in
      let* out = lift_cmp @@ do_el_out con in
      quote_con unfolded out
    in
    S.ElIn tout

  | _, D.Zero ->
    ret S.Zero

  | _, D.Suc n ->
    let+ tn = quote_con D.Nat n in
    S.Suc tn

  | D.TpDim, D.DimCon0 ->
    ret @@ S.Dim0

  | D.TpDim, D.DimCon1 ->
    ret @@ S.Dim1

  | D.TpCof, D.Cof cof ->
    let* phi = lift_cmp @@ cof_con_to_cof cof in
    quote_cof phi

  | D.TpPrf _, _ ->
    ret S.Prf

  | _, D.CodeNat ->
    ret S.CodeNat

  | _, D.CodeUniv ->
    ret S.CodeUniv

  | univ, D.CodePi (base, fam) ->
    let+ tbase = quote_con univ base
    and+ tfam =
      QTB.lam (D.El base) @@ fun var ->
      quote_con univ @<<
      lift_cmp @@ do_ap fam var
    in
    S.CodePi (tbase, tfam)

  | univ, D.CodeSg (base, fam) ->
    let+ tbase = quote_con univ base
    and+ tfam =
      QTB.lam (D.El base) @@ fun var ->
      quote_con univ @<<
      lift_cmp @@ do_ap fam var
    in
    S.CodeSg (tbase, tfam)

    (*
    *  path : (fam : I -> U) -> ((i : I) -> (p : [i=0\/i=1]) -> fam i) -> U
    * *)
  | univ, D.CodePath (fam, bdry) -> (* check *)
    let* piuniv =
      lift_cmp @@
      splice_tp @@
      Splice.foreign_tp univ @@ fun univ ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      univ
    in
    let* tfam = quote_con piuniv fam in
    (* (i : I) -> (p : [i=0\/i=1]) -> fam i  *)
    let* bdry_tp =
      lift_cmp @@
      splice_tp @@
      Splice.foreign_tp univ @@ fun univ ->
      Splice.foreign fam @@ fun fam ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.boundary i)) @@ fun prf ->
      TB.el @@ TB.ap fam [i]
    in
    let+ tbdry = quote_con bdry_tp bdry in
    S.CodePath (tfam, tbdry)

  | D.Nat, D.FHCom (`Nat, r, s, phi, bdy) ->
    (* bdy : (i : 𝕀) (_ : [...]) → nat *)
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let+ tm = quote_hcom D.CodeNat r s phi bdy' in
    S.ElOut tm

  | _ ->
    throw @@ QuotationError (Error.IllTypedQuotationProblem (tp, con))

and quote_hcom code r s phi bdy =
  let* tcode = quote_con D.Univ code in
  let* tr = quote_dim r in
  let* ts = quote_dim s in
  let* tphi = quote_cof phi in
  let+ tbdy =
    QTB.lam D.TpDim @@ fun i ->
    let* i_dim = lift_cmp @@ con_to_dim i in
    QTB.lam (D.TpPrf (Cof.join [Cof.eq r i_dim; phi])) @@ fun prf ->
    let* body = lift_cmp @@ do_ap2 bdy i prf in
    quote_con (D.El code) body
  in
  S.HCom (tcode, tr, ts, tphi, tbdy)

and quote_tp_clo base fam =
  bind_var ~abort:(S.El S.CofAbort) base @@ fun var ->
  quote_tp @<< lift_cmp @@ inst_tp_clo fam var

and quote_tp (tp : D.tp) =
  match tp with
  | D.TpAbort -> ret @@ S.El S.CofAbort
  | D.Nat -> ret S.Nat
  | D.Pi (base, ident, fam) ->
    let* tbase = quote_tp base in
    let+ tfam = quote_tp_clo base fam in
    S.Pi (tbase, ident, tfam)
  | D.Sg (base, ident, fam) ->
    let* tbase = quote_tp base in
    let+ tfam = quote_tp_clo base fam in
    S.Sg (tbase, ident, tfam)
  | D.Univ ->
    ret S.Univ
  | D.UnfoldEl cut ->
    let+ tm = quote_cut cut in
    S.UnfoldEl tm
  | D.El con ->
    let+ tm = quote_con D.Univ con in
    S.El tm
  | D.GoalTp (lbl, tp) ->
    let+ tp = quote_tp tp in
    S.GoalTp (lbl, tp)
  | D.Sub (tp, phi, cl) ->
    let* ttp = quote_tp tp in
    let+ tphi = quote_cof phi
    and+ tm =
      bind_var ~abort:S.CofAbort (D.TpPrf phi) @@ fun prf ->
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
  | D.TpHCom (r, s, phi, bdy) ->
    raise CCHM


and quote_hd =
  function
  | D.Var lvl ->
    let+ n = read_local in
    S.Var (n - (lvl + 1))
  | D.Global sym ->
    ret @@ S.Global sym
  | D.Coe (abs, r, s, con) ->
    let* tpcode =
      QTB.lam D.TpDim @@ fun i ->
      quote_con D.Univ @<< lift_cmp @@ do_ap abs i
    in
    let* tr = quote_dim r in
    let* ts = quote_dim s in
    let* code_r = lift_cmp @@ do_ap abs @@ D.dim_to_con r in
    let+ tm = quote_con (D.El code_r) con in
    S.Coe (tpcode, tr, ts, tm)
  | D.HCom (cut, r, s, phi, bdy) ->
    let code = D.Cut {cut; tp = D.Univ} in
    quote_hcom code r s phi bdy
  | D.SubOut (cut, phi, clo) ->
    let+ tm = quote_cut cut in
    S.SubOut tm
  | D.Split (tp, branches) ->
    let branch_body (phi, clo) =
      begin
        bind_var ~abort:S.CofAbort (D.TpPrf phi) @@ fun prf ->
        let* body = lift_cmp @@ inst_tm_clo clo prf in
        quote_con tp body
      end
    in
    let* ttp = quote_tp tp in
    let* tphis = MU.map (fun (phi , _) -> quote_cof phi) branches in
    let* tms = MU.map branch_body branches in
    ret @@ S.CofSplit (ttp, List.combine tphis tms)
  | D.Cap _ ->
    raise CFHM


and quote_dim d =
  quote_con D.TpDim @@
  D.dim_to_con d

and quote_cof phi =
  let rec go =
    function
    | Cof.Var lvl ->
      let+ ix = quote_var lvl in
      S.Var ix
    | Cof.Cof phi ->
      match phi with
      | Cof.Eq (r, s) ->
        let+ tr = quote_dim r
        and+ ts = quote_dim s in
        S.Cof (Cof.Eq (tr, ts))
      | Cof.Join phis ->
        let+ tphis = MU.map go phis in
        S.Cof (Cof.Join tphis)
      | Cof.Meet phis ->
        let+ tphis = MU.map go phis in
        S.Cof (Cof.Meet tphis)
  in
  go @<< lift_cmp @@ Sem.normalize_cof phi

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
      quote_con (D.El mot_zero) zero_case
    in
    let* suc_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.foreign mot @@ fun mot ->
      Splice.term @@
      TB.pi TB.nat @@ fun x ->
      TB.pi (TB.el (TB.ap mot [x])) @@ fun ih ->
      TB.el @@ TB.ap mot [TB.suc x]
    in
    let* tsuc_case = quote_con suc_tp suc_case in
    ret @@ S.NatElim (tmot, tzero_case, tsuc_case, tm)
  | D.KFst ->
    ret @@ S.Fst tm
  | D.KSnd ->
    ret @@ S.Snd tm
  | D.KAp (tp, con) ->
    let+ targ = quote_con tp con in
    S.Ap (tm, targ)
  | D.KGoalProj ->
    ret @@ S.GoalProj tm
  | D.KElOut ->
    ret @@ S.ElOut tm
