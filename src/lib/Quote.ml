module S = Syntax
module D = Domain
module Sem = Semantics
module TB = TermBuilder

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

open Sem

let contractum_or x =
  function
  | `Done -> x
  | `Reduce y -> y

let rec quote_con (tp : D.tp) con =
  let open QuM in
  let open Monad.Notation (QuM) in
  let module MU = Monad.Util (QuM) in
  QuM.abort_if_inconsistent (ret S.tm_abort) @@
  let* tp = contractum_or tp <@> lift_cmp @@ Sem.whnf_tp tp in
  let* con = contractum_or con <@> lift_cmp @@ Sem.whnf_con con in
  match tp, con with
  | _, D.Split branches ->
    let branch_body (phi, clo) =
      bind_var (D.TpPrf phi) @@ fun prf ->
      let* body = lift_cmp @@ inst_tm_clo clo prf in
      quote_con tp body
    in
    let* tphis = MU.map (fun (phi , _) -> quote_cof phi) branches in
    let* tms = MU.map branch_body branches in
    ret @@ S.CofSplit (List.combine tphis tms)
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

  | _, D.Zero ->
    ret S.Zero

  | _, D.Suc n ->
    let+ tn = quote_con D.Nat n in
    S.Suc tn

  | _, D.Base ->
    ret S.Base

  | D.TpDim, D.DimCon0 ->
    ret @@ S.Dim0

  | D.TpDim, D.DimCon1 ->
    ret @@ S.Dim1

  | D.TpCof, D.Cof cof ->
    let* cof = lift_cmp @@ cof_con_to_cof cof in
    quote_cof cof

  | D.TpPrf _, _ ->
    ret S.Prf

  | _, D.CodeNat ->
    ret S.CodeNat

  | _, D.CodeCircle ->
    ret S.CodeCircle

  | _, D.CodeUniv ->
    ret S.CodeUniv

  | _ ->
    seq ~splitter:con_splitter @@ split_quote_whnf_con tp con

and split_quote_con tp con = QuM.split [] @@ quote_con tp con

and split_quote_lam ?(ident = `Anon) tp mbdy =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let+ bdy = bind_var ~splitter:con_splitter tp mbdy in
  S.Lam (ident, bdy)

and con_splitter tbranches =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let module MU = Monad.Util (SplitQuM) in
  let* filtered =
    List.flatten <@>
    begin
      tbranches |> MU.map @@ fun (cof, m) ->
      lift_cmp (CmpM.test_sequent [cof] Cof.bot) |>> function
      | true ->
        ret []
      | false ->
        ret [cof,m]
    end
  in

  match filtered with
  | [cof,m] -> m
  | _ ->
    let run_branch (cof, m) =
      let+ tm = binder 1 m
      and+ tcof = split_quote_cof cof in
      tcof, tm
    in
    let+ branches = MU.map run_branch filtered in
    S.CofSplit branches

and split_quote_whnf_con (tp : D.tp) con =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let module MU = Monad.Util (SplitQuM) in
  match tp, con with
  | _, D.Cut {cut = (D.Global sym, sp) as cut; tp} ->
    let* st = SplitQuM.read_global in
    let* veil = SplitQuM.read_veil in
    begin
      let _, ocon = ElabState.get_global sym st in
      begin
        match ocon, Veil.policy sym veil with
        | Some con, `Transparent ->
          let* con' = lift_cmp @@ Sem.do_spine con sp in
          split_quote_con tp con'
        | _ ->
          split_quote_cut cut
      end
    end

  | _, D.Cut {cut = (hd, sp); tp} ->
    split_quote_cut (hd, sp)

  | D.Pi (base, _, fam), D.Lam (ident, clo) ->
    split_quote_lam ~ident base @@ fun arg ->
    let* fib = lift_cmp @@ inst_tp_clo fam arg in
    let* ap = lift_cmp @@ inst_tm_clo clo arg in
    split_quote_con fib ap

  | D.Pi (base, ident, fam), con ->
    split_quote_lam ~ident base @@ fun arg ->
    let* fib = lift_cmp @@ inst_tp_clo fam arg in
    let* ap = lift_cmp @@ do_ap con arg in
    split_quote_con fib ap

  | D.Sg (base, _, fam), _ ->
    let* fst = lift_cmp @@ do_fst con in
    let* snd = lift_cmp @@ do_snd con in
    let* fib = lift_cmp @@ inst_tp_clo fam fst in
    let+ tfst = split_quote_con base fst
    and+ tsnd = split_quote_con fib snd in
    S.Pair (tfst, tsnd)

  | D.Sub (tp, phi, clo), _ ->
    let+ tout =
      let* out = lift_cmp @@ do_sub_out con in
      split_quote_con tp out
    in
    S.SubIn tout

  | D.El code, _ ->
    let+ tout =
      let* unfolded = lift_cmp @@ unfold_el code in
      let* out = lift_cmp @@ do_el_out con in
      split_quote_con unfolded out
    in
    S.ElIn tout

  | _, D.Loop r ->
    let+ tr = split_quote_dim r in
    S.Loop tr

  | univ, D.CodePi (base, fam) ->
    let+ tbase = split_quote_con univ base
    and+ tfam =
      let* elbase = lift_cmp @@ do_el base in
      split_quote_lam elbase @@ fun var ->
      split_quote_con univ @<<
      lift_cmp @@ do_ap fam var
    in
    S.CodePi (tbase, tfam)

  | univ, D.CodeSg (base, fam) ->
    let+ tbase = split_quote_con univ base
    and+ tfam =
      let* elbase = lift_cmp @@ do_el base in
      split_quote_lam elbase @@ fun var ->
      split_quote_con univ @<<
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
    let* tfam = split_quote_con piuniv fam in
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
    let+ tbdry = split_quote_con bdry_tp bdry in
    S.CodePath (tfam, tbdry)

  | univ, D.CodeV (r, pcode, code, pequiv) ->
    let+ tr, t_pcode, tcode, t_pequiv = split_quote_v_data r pcode code pequiv in
    S.CodeV (tr, t_pcode, tcode, t_pequiv)

  | D.Nat, D.FHCom (`Nat, r, s, phi, bdy) ->
    (* bdy : (i : 𝕀) (_ : [...]) → nat *)
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let+ tm = split_quote_hcom D.CodeNat r s phi bdy' in
    S.ElOut tm

  | D.Univ, D.FHCom (`Univ, r, s, phi, bdy) ->
    (* bdy : (i : 𝕀) (_ : [...]) → nat *)
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let+ tm = split_quote_hcom D.CodeUniv r s phi bdy' in
    S.ElOut tm

  | D.Circle, D.FHCom (`Circle, r, s, phi, bdy) ->
    let* bdy' =
      lift_cmp @@ splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let+ tm = split_quote_hcom D.CodeCircle r s phi bdy' in
    S.ElOut tm

  | D.ElUnstable (`HCom (r,s,phi,bdy)), _ ->
    let+ tr = split_quote_dim r
    and+ ts = split_quote_dim s
    and+ tphi = split_quote_cof phi
    and+ tsides =
      split_quote_lam (D.TpPrf phi) @@ fun prf ->
      split_quote_con tp con
    and+ tcap =
      let* bdy_r = lift_cmp @@ do_ap2 bdy (D.dim_to_con r) D.Prf in
      let* el_bdy_r = lift_cmp @@ do_el bdy_r in
      split_quote_con el_bdy_r @<< lift_cmp @@ do_rigid_cap r s phi bdy con
    in
    S.Box (tr, ts, tphi, tsides, tcap)

  | D.ElUnstable (`V (r, pcode, code, pequiv)) as tp, _ ->
    begin
      lift_cmp (CmpM.test_sequent [] (Cof.boundary r)) |>> function
      | true ->
        restrict ~splitter:con_splitter [Cof.boundary r] @@
        (* Format.eprintf "quoting: %a |= %a / %a@." D.pp_cof phi D.pp_tp tp D.pp_con con; *)
        split_quote_con tp con
      | false ->
        let+ tr = split_quote_dim r
        and+ part =
          split_quote_lam (D.TpPrf (Cof.eq r D.Dim0)) @@ fun _ ->
          let* pcode_fib = lift_cmp @@ do_ap pcode D.Prf in
          let* tp = lift_cmp @@ do_el pcode_fib in
          split_quote_con tp con
        and+ tot =
          let* tp = lift_cmp @@ do_el code in
          let* proj = lift_cmp @@ do_rigid_vproj r pcode code pequiv con in
          split_quote_con tp proj
        and+ t_pequiv =
          let* tp_pequiv =
            lift_cmp @@ Sem.splice_tp @@
            Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
          in
          split_quote_con tp_pequiv pequiv
        in
        S.VIn (tr, t_pequiv, part, tot)
    end

  | _, D.LetSym (r, x, con) ->
    split_quote_con tp @<< lift_cmp @@ Sem.push_subst_con r x con

  | D.TpSplit branches as tp, _ ->
    let branch_body phi : S.t m =
      QuM.split [] @@
      QuM.bind_var (D.TpPrf phi) @@ fun prf ->
      quote_con tp con
    in
    let* branches =
      List.flatten <@>
      begin
        branches |> MU.map @@ fun (phi, clo) ->
        lift_cmp (CmpM.test_sequent [phi] Cof.bot) |>> function
        | true ->
          ret []
        | false ->
          ret [phi,clo]
      end
    in
    begin
      match branches with
      | [phi, tp_clo] ->
        let* tp = lift_cmp @@ inst_tp_clo tp_clo D.Prf in
        split_quote_con tp con
      | _ ->
        let phis = List.map fst branches in
        let+ tphis = MU.map split_quote_cof phis
        and+ tms = MU.map branch_body phis in
        S.CofSplit (List.combine tphis tms)
    end

  | _ ->
    Format.eprintf "bad: %a / %a@." D.pp_tp tp D.pp_con con;
    throw @@ QuotationError (Error.IllTypedQuotationProblem (tp, con))

and split_quote_v_data r pcode code pequiv =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let+ tr = split_quote_dim r
  and+ t_pcode = split_quote_con (D.Pi (D.TpPrf (Cof.eq r D.Dim0), `Anon, D.const_tp_clo D.Univ)) pcode
  and+ tcode = split_quote_con D.Univ code
  and+ t_pequiv =
    let* tp_pequiv =
      lift_cmp @@ Sem.splice_tp @@
      Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
    in
    split_quote_con tp_pequiv pequiv
  in
  tr, t_pcode, tcode, t_pequiv


and split_quote_hcom code r s phi bdy =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let* tcode = split_quote_con D.Univ code in
  let* tr = split_quote_dim r in
  let* ts = split_quote_dim s in
  let* tphi = split_quote_cof phi in
  let+ tbdy =
    split_quote_lam D.TpDim @@ fun i ->
    let* i_dim = lift_cmp @@ con_to_dim i in
    split_quote_lam (D.TpPrf (Cof.join [Cof.eq r i_dim; phi])) @@ fun prf ->
    let* body = lift_cmp @@ do_ap2 bdy i prf in
    let* tp = lift_cmp @@ do_el code in
    split_quote_con tp body
  in
  S.HCom (tcode, tr, ts, tphi, tbdy)

and split_quote_tp_clo base fam =
  let open QuM in
  let open Monad.Notation (QuM) in
  QuM.split [] @@ QuM.bind_var base @@ fun var ->
  let* tp = lift_cmp @@ inst_tp_clo fam var in
  quote_tp tp

and split_quote_tp (tp : D.tp) =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let module MU = Monad.Util (SplitQuM) in
  match tp with
  | D.Nat -> ret S.Nat
  | D.Circle -> ret S.Circle
  | D.Pi (base, ident, fam) ->
    let* tbase = split_quote_tp base in
    let+ tfam = split_quote_tp_clo base fam in
    S.Pi (tbase, ident, tfam)
  | D.Sg (base, ident, fam) ->
    let* tbase = split_quote_tp base in
    let+ tfam = split_quote_tp_clo base fam in
    S.Sg (tbase, ident, tfam)
  | D.Univ ->
    ret S.Univ
  | D.El con ->
    let+ tm = split_quote_con D.Univ con in
    S.El tm
  | D.ElCut cut ->
    let+ tm = split_quote_cut cut in
    S.El tm
  | D.GoalTp (lbl, tp) ->
    let+ tp = split_quote_tp tp in
    S.GoalTp (lbl, tp)
  | D.Sub (tp, phi, cl) ->
    let* ttp = split_quote_tp tp in
    let+ tphi = split_quote_cof phi
    and+ tm =
      let open QuM in
      let open Monad.Notation (QuM) in
      QuM.split [] @@
      QuM.bind_var (D.TpPrf phi) @@ fun prf ->
      let* body = lift_cmp @@ inst_tm_clo cl prf in
      quote_con tp body
    in
    S.Sub (ttp, tphi, tm)
  | D.TpDim ->
    ret S.TpDim
  | D.TpCof ->
    ret S.TpCof
  | D.TpPrf phi ->
    let+ tphi = split_quote_cof phi in
    S.TpPrf tphi
  | D.ElUnstable (`HCom (r, s, phi, bdy)) ->
    let+ tr = split_quote_dim r
    and+ ts = split_quote_dim s
    and+ tphi = split_quote_cof phi
    and+ tbdy =
      let* tp_bdy =
        lift_cmp @@
        Sem.splice_tp @@
        Splice.foreign_dim r @@ fun r ->
        Splice.foreign_cof phi @@ fun phi ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun prf ->
        TB.univ
      in
      split_quote_con tp_bdy bdy
    in
    S.El (S.HCom (S.CodeUniv, tr, ts, tphi, tbdy))
  | D.ElUnstable (`V (r, pcode, code, pequiv)) ->
    let+ tr, t_pcode, tcode, t_pequiv = split_quote_v_data r pcode code pequiv in
    S.El (S.CodeV (tr, t_pcode, tcode, t_pequiv))
  | D.TpSplit branches ->
    let branch_body (phi, clo) : S.tp m =
      let open QuM in
      let open Monad.Notation (QuM) in
      QuM.split [] @@
      QuM.bind_var (D.TpPrf phi) @@ fun prf ->
      let* tp = lift_cmp @@ inst_tp_clo clo prf in
      quote_tp tp
    in
    let+ tphis = MU.map (fun (phi , _) -> split_quote_cof phi) branches
    and+ tps = MU.map branch_body branches in
    S.TpCofSplit (List.combine tphis tps)

and tp_splitter tbranches =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  let module MU = Monad.Util (SplitQuM) in
  let run_branch (cof, m) =
    let+ tm = binder 1 m
    and+ tcof = split_quote_cof cof in
    tcof, tm
  in
  let+ tbranches = MU.map run_branch tbranches in
  S.TpCofSplit tbranches

and quote_tp tp =
  QuM.seq ~splitter:tp_splitter @@ split_quote_tp tp

and split_quote_hd =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  function
  | D.Var lvl ->
    let+ i = split_quote_var lvl in
    S.Var i
  | D.Global sym ->
    ret @@ S.Global sym
  | D.Coe (code, r, s, con) ->
    let code_tp = D.Pi (D.TpDim, `Anon, D.const_tp_clo D.Univ) in
    let* tpcode = split_quote_con code_tp code in
    let* tr = split_quote_dim r in
    let* ts = split_quote_dim s in
    let* code_r = lift_cmp @@ do_ap code @@ D.dim_to_con r in
    let* tp_code_r = lift_cmp @@ do_el code_r in
    let+ tm = split_quote_con tp_code_r con in
    S.Coe (tpcode, tr, ts, tm)
  | D.HCom (cut, r, s, phi, bdy) ->
    let code = D.Cut {cut; tp = D.Univ} in
    split_quote_hcom code r s phi bdy
  | D.SubOut (cut, phi, clo) ->
    let+ tm = split_quote_cut cut in
    S.SubOut tm
  | D.Cap (r, s, phi, code, box) ->
    let* tr = split_quote_dim r in
    let* ts = split_quote_dim s in
    let* tphi = split_quote_cof phi in
    let* code_tp =
      lift_cmp @@
      Sem.splice_tp @@
      Splice.foreign_dim r @@ fun r ->
      Splice.foreign_cof phi @@ fun phi ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun prf ->
      TB.univ
    in
    let+ tcode = split_quote_con code_tp code
    and+ tbox = split_quote_cut box in
    S.Cap (tr, ts, tphi, tcode, tbox)
  | D.VProj (r, pcode, code, pequiv, v) ->
    let* tr = split_quote_dim r in
    let* tpcode = split_quote_con (D.Pi (D.TpPrf (Cof.eq r D.Dim0), `Anon, D.const_tp_clo D.Univ)) pcode in
    let* tcode = split_quote_con D.Univ code in
    let* t_pequiv =
      let* tp_pequiv =
        lift_cmp @@ Sem.splice_tp @@
        Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
      in
      split_quote_con tp_pequiv pequiv
    in
    let+ tv = split_quote_cut v in
    S.VProj (tr, tpcode, tcode, t_pequiv, tv)


and split_quote_dim d : S.t split_quote =
  QuM.split [] @@
  quote_dim d

and quote_dim d : S.t quote =
  quote_con D.TpDim @@
  D.dim_to_con d

and quote_cof phi =
  let open QuM in
  let open Monad.Notation (QuM) in
  let module MU = Monad.Util (QuM) in
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

and split_quote_cof cof =
  QuM.split [] @@ quote_cof cof

and split_quote_var lvl =
  QuM.split [] @@ quote_var lvl

and quote_var lvl =
  let open QuM in
  let open Monad.Notation (QuM) in
  let+ n = read_local in
  n - (lvl + 1)

and split_quote_cut (hd, spine) =
  let open Monad.Notation (SplitQuM) in
  let* tm = split_quote_hd hd in
  split_quote_spine tm spine

and quote_cut cut =
  QuM.seq ~splitter:con_splitter @@ split_quote_cut cut

and split_quote_spine tm =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  function
  | [] -> ret tm
  | k :: spine ->
    let* tm' = split_quote_frm tm k in
    split_quote_spine tm' spine

and split_quote_frm tm =
  let open SplitQuM in
  let open Monad.Notation (SplitQuM) in
  function
  | D.KNatElim (mot, zero_case, suc_case) ->
    let* mot_tp =
      lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.nat @@ fun _ -> TB.univ
    in
    let* tmot = split_quote_con mot_tp mot in
    let* tzero_case =
      let* mot_zero = lift_cmp @@ do_ap mot D.Zero in
      let* tp_mot_zero = lift_cmp @@ do_el mot_zero in
      split_quote_con tp_mot_zero zero_case
    in
    let* suc_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.foreign mot @@ fun mot ->
      Splice.term @@
      TB.pi TB.nat @@ fun x ->
      TB.pi (TB.el (TB.ap mot [x])) @@ fun ih ->
      TB.el @@ TB.ap mot [TB.suc x]
    in
    let* tsuc_case = split_quote_con suc_tp suc_case in
    ret @@ S.NatElim (tmot, tzero_case, tsuc_case, tm)
  | D.KCircleElim (mot, base_case, loop_case) ->
    let* mot_tp =
      lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.circle @@ fun _ -> TB.univ
    in
    let* tmot = split_quote_con mot_tp mot in
    let* tbase_case =
      let* mot_base = lift_cmp @@ do_ap mot D.Base in
      let* tp_mot_base = lift_cmp @@ do_el mot_base in
      split_quote_con tp_mot_base base_case
    in
    let* loop_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.foreign mot @@ fun mot ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun x ->
      TB.el @@ TB.ap mot [TB.loop x]
    in
    let* tloop_case = split_quote_con loop_tp loop_case in
    ret @@ S.CircleElim (tmot, tbase_case, tloop_case, tm)
  | D.KFst ->
    ret @@ S.Fst tm
  | D.KSnd ->
    ret @@ S.Snd tm
  | D.KAp (tp, con) ->
    let+ targ = split_quote_con tp con in
    S.Ap (tm, targ)
  | D.KGoalProj ->
    ret @@ S.GoalProj tm
  | D.KElOut ->
    ret @@ S.ElOut tm
