module S = Syntax
module D = Domain
module Sem = Semantics


exception Todo

open CoolBasis
open Monads

exception NbeFailed of string

module Splice = Splice
module TB = TermBuilder

module Quote : sig
  val quote_con : D.tp -> D.con -> S.t quote
  val quote_cof : D.cof -> S.t quote
  val quote_tp : D.tp -> S.tp quote
  val equal_con : D.tp -> D.con -> D.con -> bool quote
  val quote_cut : D.cut -> S.t quote
  val equal_tp : D.tp -> D.tp -> bool quote
  val equate_con : D.tp -> D.con -> D.con -> unit quote
  val equate_tp : D.tp -> D.tp -> unit quote
end =
struct
  open QuM
  open Monad.Notation (QuM)
  open Sem

  let top_var tp =
    let+ n = read_local in
    D.mk_var tp @@ n - 1

  let top_dim_var =
    let+ n = read_local in
    D.DimVar (n - 1)


  let bind_var abort tp m =
    match tp with
    | D.TpPrf phi ->
      begin
        begin
          bind_cof_proof phi @@
          let* var = top_var tp in
          m var
        end |>> function
        | `Ret tm -> ret tm
        | `Abort -> ret abort
      end
    | _ ->
      binder 1 @@
      let* var = top_var tp in
      m var

  let rec quote_con (tp : D.tp) con : S.t m =
    QuM.abort_if_inconsistent S.CofAbort @@
    match tp, con with
    | _, D.Abort -> ret S.CofAbort
    | _, D.Cut {cut = (D.Var lvl, []); tp = TpDim} ->
      (* for dimension variables, check to see if we can prove them to be
         the same as 0 or 1 and return those instead if so. *)
      begin
        lift_cmp @@ CmpM.test_sequent [] @@ Cof.eq (D.DimVar lvl) D.Dim0 |>> function
        | true -> ret S.Dim0
        | false ->
          lift_cmp @@ CmpM.test_sequent [] (Cof.eq (D.DimVar lvl) D.Dim1) |>> function
          | true -> ret S.Dim1
          | false ->
            let+ ix = quote_var lvl in
            S.Var ix
      end
    | _, D.Cut {cut = (hd, sp); tp} ->
      quote_cut (hd, sp)
    | D.Pi (base, fam), con ->
      let+ body =
        bind_var S.CofAbort base @@ fun arg ->
        let* fib = lift_cmp @@ inst_tp_clo fam [arg] in
        let* ap = lift_cmp @@ do_ap con arg in
        quote_con fib ap
      in
      S.Lam body
    | D.Sg (base, fam), _ ->
      let* fst = lift_cmp @@ do_fst con in
      let* snd = lift_cmp @@ do_snd con in
      let* fib = lift_cmp @@ inst_tp_clo fam [fst] in
      let+ tfst = quote_con base fst
      and+ tsnd = quote_con fib snd in
      S.Pair (tfst, tsnd)
    | D.Sub (tp, phi, clo), _ ->
      let+ tout =
        let* out = lift_cmp @@ do_sub_out con in
        quote_con tp out
      in
      S.SubIn tout
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

    | univ, D.CodePi (base, fam) ->
      let+ tbase = quote_con univ base
      and+ tfam =
        let* tpbase = lift_cmp @@ do_el base in
        let+ bdy =
          bind_var S.CofAbort tpbase @@ fun var ->
          quote_con univ @<<
          lift_cmp @@ do_ap fam var
        in
        S.Lam bdy
      in
      S.CodePi (tbase, tfam)
    | univ, D.CodeSg (base, fam) ->
      let+ tbase = quote_con univ base
      and+ tfam =
        let* tpbase = lift_cmp @@ do_el base in
        let+ bdy =
          bind_var S.CofAbort tpbase @@ fun var ->
          quote_con univ @<<
          lift_cmp @@ do_ap fam var
        in
        S.Lam bdy
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

    | _, D.FHCom (`Nat, r, s, phi, bdy) ->
      quote_hcom D.CodeNat r s phi bdy

    | _ ->
      Format.eprintf "bad: %a / %a@." D.pp_tp tp D.pp_con con;
      throw @@ NbeFailed "ill-typed quotation problem"

  and quote_hcom code r s phi bdy =
    let* tcode = quote_con D.Univ code in
    let* tp = lift_cmp @@ do_el code in
    let* tr = quote_dim r in
    let* ts = quote_dim s in
    let* tphi = quote_cof phi in
    let+ tbdy =
      let+ tm =
        bind_var S.CofAbort D.TpDim @@ fun i ->
        begin
          let* i_dim = lift_cmp @@ con_to_dim i in
          bind_cof_proof (Cof.join (Cof.eq r i_dim) phi) @@
          let* body = lift_cmp @@ do_ap2 bdy i D.Prf in
          quote_con D.Nat body
        end |>> function
        | `Ret tm -> ret tm
        | `Abort -> ret S.CofAbort
      in
      S.Lam (S.Lam tm)
    in
    S.HCom (tcode, tr, ts, tphi, tbdy)


  and quote_tp (tp : D.tp) =
    match tp with
    | D.TpAbort -> ret @@ S.El S.CofAbort
    | D.Nat -> ret S.Nat
    | D.Pi (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam =
        bind_var (S.El S.CofAbort) base @@ fun var ->
        quote_tp @<< lift_cmp @@ inst_tp_clo fam [var]
      in
      S.Pi (tbase, tfam)
    | D.Sg (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam =
        bind_var (S.El S.CofAbort) base @@ fun var ->
        quote_tp @<< lift_cmp @@ inst_tp_clo fam [var]
      in
      S.Sg (tbase, tfam)
    | D.Univ ->
      ret S.Univ
    | D.El cut ->
      let+ tm = quote_cut cut in
      S.El tm
    | D.GoalTp (lbl, tp) ->
      let+ tp = quote_tp tp in
      S.GoalTp (lbl, tp)
    | D.Sub (tp, phi, cl) ->
      let* ttp = quote_tp tp in
      let+ tphi = quote_cof phi
      and+ tm =
        begin
          bind_cof_proof phi @@
          let* body = lift_cmp @@ inst_tm_clo cl [D.Prf] in
          quote_con tp body
        end |>> function
        | `Ret tm -> ret tm
        | `Abort -> ret S.CofAbort
      in
      S.Sub (ttp, tphi, tm)
    | D.TpDim ->
      ret S.TpDim
    | D.TpCof ->
      ret S.TpCof
    | D.TpPrf phi ->
      let+ tphi = quote_cof phi in
      S.TpPrf tphi


  and quote_hd =
    function
    | D.Var lvl ->
      let+ n = read_local in
      S.Var (n - (lvl + 1))
    | D.Global sym ->
      ret @@ S.Global sym
    | D.Coe (abs, r, s, con) ->
      let* tpcode =
        let+ bdy =
          bind_var S.CofAbort D.TpDim @@ fun i ->
          let* code = lift_cmp @@ do_ap abs i in
          quote_con D.Univ code
        in
        S.Lam bdy
      in
      let* tr = quote_dim r in
      let* ts = quote_dim s in
      let* tp_con_r = lift_cmp @@ do_ap abs @@ D.dim_to_con r in
      let* tp_r = lift_cmp @@ do_el tp_con_r in
      let+ tm = quote_con tp_r con in
      S.Coe (tpcode, tr, ts, tm)
    | D.HCom (cut, r, s, phi, bdy) ->
      let code = D.Cut {cut; tp = D.Univ} in
      quote_hcom code r s phi bdy
    | D.SubOut (cut, phi, clo) ->
      let+ tm = quote_cut cut in
      S.SubOut tm
    | D.Split (tp, phi0, phi1, clo0, clo1) ->
      let branch_body phi clo =
        begin
          bind_cof_proof phi @@
          let* body = lift_cmp @@ inst_tm_clo clo [D.Prf] in
          quote_con tp body
        end |>> function
        | `Ret tm -> ret tm
        | `Abort -> ret S.CofAbort
      in
      let* ttp = quote_tp tp in
      let* tphi0 = quote_cof phi0 in
      let* tphi1 = quote_cof phi1 in
      let* tm0 = branch_body phi0 clo0 in
      let* tm1 = branch_body phi1 clo1 in
      ret @@ S.CofSplit (ttp, tphi0, tphi1, tm0, tm1)

  and quote_dim d = quote_con D.TpDim @@ D.dim_to_con d

  and quote_cof =
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
      | Cof.Join (phi, psi) ->
        let+ tphi = quote_cof phi
        and+ tpsi = quote_cof psi in
        S.Cof (Cof.Join (tphi, tpsi))
      | Cof.Meet (phi, psi) ->
        let+ tphi = quote_cof phi
        and+ tpsi = quote_cof psi in
        S.Cof (Cof.Meet (tphi, tpsi))
      | Cof.Bot ->
        ret @@ S.Cof Cof.Bot
      | Cof.Top ->
        ret @@ S.Cof Cof.Top

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
      let* mot_x =
        bind_var D.TpAbort D.Nat @@ fun x ->
        lift_cmp @@ inst_tp_clo mot [x]
      in
      let* tmot =
        bind_var (S.El S.CofAbort) D.Nat @@ fun _ ->
        quote_tp mot_x
      in
      let+ tzero_case =
        let* mot_zero = lift_cmp @@ inst_tp_clo mot [D.Zero] in
        quote_con mot_zero zero_case
      and+ tsuc_case =
        bind_var S.CofAbort D.Nat @@ fun x ->
        bind_var S.CofAbort mot_x @@ fun ih ->
        let* mot_suc_x = lift_cmp @@ inst_tp_clo mot [D.Suc x] in
        let* suc_case_x = lift_cmp @@ inst_tm_clo suc_case [x; ih] in
        quote_con mot_suc_x suc_case_x
      in
      S.NatElim (tmot, tzero_case, tsuc_case, tm)
    | D.KFst ->
      ret @@ S.Fst tm
    | D.KSnd ->
      ret @@ S.Snd tm
    | D.KAp (tp, con) ->
      let+ targ = quote_con tp con in
      S.Ap (tm, targ)
    | D.KGoalProj ->
      ret @@ S.GoalProj tm


  let equate_dim r s =
    CmpM.test_sequent [] (Cof.eq r s) |> lift_cmp |>> function
    | true -> ret ()
    | false -> throw @@ NbeFailed "Expected dimensions to be equal"

  let contractum_or x =
    function
    | `Done -> x
    | `Reduce y -> y



  let bind_var_ tp m =
    match tp with
    | D.TpPrf phi ->
      begin
        begin
          bind_cof_proof phi @@
          let* var = top_var tp in
          QuM.left_invert_under_cof phi @@
          m var
        end |>> function
        | `Ret _ -> ret ()
        | `Abort -> ret ()
      end
    | _ ->
      binder 1 @@
      let* var = top_var tp in
      m var


  (* Invariant: tp0 and tp1 not necessarily whnf *)
  let rec equate_tp (tp0 : D.tp) (tp1 : D.tp) =
    QuM.abort_if_inconsistent () @@
    let* tp0 = contractum_or tp0 <@> lift_cmp @@ whnf_tp tp0 in
    let* tp1 = contractum_or tp1 <@> lift_cmp @@ whnf_tp tp1 in
    match tp0, tp1 with
    | D.TpAbort, _ | _, D.TpAbort -> ret ()
    | D.TpDim, D.TpDim | D.TpCof, D.TpCof -> ret ()
    | D.TpPrf phi0, D.TpPrf phi1 ->
      equate_cof phi0 phi1
    | D.Pi (base0, fam0), D.Pi (base1, fam1)
    | D.Sg (base0, fam0), D.Sg (base1, fam1) ->
      let* () = equate_tp base0 base1 in
      bind_var_ base0 @@ fun x ->
      let* fib0 = lift_cmp @@ inst_tp_clo fam0 [x] in
      let* fib1 = lift_cmp @@ inst_tp_clo fam1 [x] in
      equate_tp fib0 fib1
    | D.Sub (tp0, phi0, clo0), D.Sub (tp1, phi1, clo1) ->
      let* () = equate_tp tp0 tp1 in
      let* () = equate_cof phi0 phi1 in
      bind_var_ (D.TpPrf phi0) @@ fun prf ->
      let* con0 = lift_cmp @@ inst_tm_clo clo0 [prf] in
      let* con1 = lift_cmp @@ inst_tm_clo clo1 [prf] in
      equate_con tp0 con0 con1
    | D.Nat, D.Nat
    | D.Univ, D.Univ ->
      ret ()
    | D.GoalTp (lbl0, tp0), D.GoalTp (lbl1, tp1) when lbl0 = lbl1 ->
      equate_tp tp0 tp1
    | D.El cut0, D.El cut1 ->
      equate_cut cut0 cut1
    | _ ->
      throw @@ NbeFailed "unequal types"

  (* Invariant: tp, con0, con1 not necessarily whnf *)
  and equate_con tp con0 con1 =
    QuM.abort_if_inconsistent () @@
    let* tp = contractum_or tp <@> lift_cmp @@ whnf_tp tp in
    let* con0 = contractum_or con0 <@> lift_cmp @@ whnf_con con0 in
    let* con1 = contractum_or con1 <@> lift_cmp @@ whnf_con con1 in
    match tp, con0, con1 with
    | D.TpPrf _, _, _ -> ret ()
    | _, D.Abort, _ -> ret ()
    | _, _, D.Abort -> ret ()
    | _, D.Cut {cut = D.Split (_, phi0, phi1, _, _), _}, _
    | _, _, D.Cut {cut = D.Split (_, phi0, phi1, _, _), _} ->
      QuM.left_invert_under_cof (Cof.join phi0 phi1) @@
      equate_con tp con0 con1
    | D.Pi (base, fam), _, _ ->
      bind_var_ base @@ fun x ->
      let* fib = lift_cmp @@ inst_tp_clo fam [x] in
      let* ap0 = lift_cmp @@ do_ap con0 x in
      let* ap1 = lift_cmp @@ do_ap con1 x in
      equate_con fib ap0 ap1
    | D.Sg (base, fam), _, _ ->
      let* fst0 = lift_cmp @@ do_fst con0 in
      let* fst1 = lift_cmp @@ do_fst con1 in
      let* () = equate_con base fst0 fst1 in
      let* fib = lift_cmp @@ inst_tp_clo fam [fst0] in
      let* snd0 = lift_cmp @@ do_snd con0 in
      let* snd1 = lift_cmp @@ do_snd con1 in
      equate_con fib snd0 snd1
    | D.GoalTp (_, tp), _, _ ->
      let* con0 = lift_cmp @@ do_goal_proj con0 in
      let* con1 = lift_cmp @@ do_goal_proj con1 in
      equate_con tp con0 con1
    | D.Sub (tp, phi, _), _, _ ->
      let* out0 = lift_cmp @@ do_sub_out con0 in
      let* out1 = lift_cmp @@ do_sub_out con1 in
      equate_con tp out0 out1
    | _, D.Zero, D.Zero ->
      ret ()
    | _, D.Suc con0, D.Suc con1 ->
      equate_con tp con0 con1
    | D.TpDim, _, _ ->
      let* r0 = lift_cmp @@ con_to_dim con0 in
      let* r1 = lift_cmp @@ con_to_dim con1 in
      approx_cof Cof.top @@ Cof.eq r0 r1
    | D.TpCof, _, _ ->
      let* phi0 = lift_cmp @@ con_to_cof con0 in
      let* phi1 = lift_cmp @@ con_to_cof con1 in
      equate_cof phi0 phi1
    | _, D.Cut {cut = cut0}, D.Cut {cut = cut1} ->
      equate_cut cut0 cut1
    | _, D.FHCom (`Nat, r0, s0, phi0, bdy0), D.FHCom (`Nat, r1, s1, phi1, bdy1) ->
      equate_hcom (D.CodeNat, r0, s0, phi0, bdy0) (D.CodeNat, r1, s1, phi1, bdy1)
    | _, D.CodeNat, D.CodeNat ->
      ret ()

    | univ, D.CodePi (base0, fam0), D.CodePi (base1, fam1)
    | univ, D.CodeSg (base0, fam0), D.CodeSg (base1, fam1) ->
      let* _ = equate_con univ base0 base1 in
      let* fam_tp =
        lift_cmp @@
        splice_tp @@
        Splice.foreign base0 @@ fun base ->
        Splice.foreign_tp univ @@ fun univ ->
        Splice.term @@ TB.pi (TB.el base) @@ fun _ -> univ
      in
      equate_con fam_tp fam0 fam1

    | univ, D.CodePath (fam0, bdry0), D.CodePath (fam1, bdry1) ->
      let* famtp =
        lift_cmp @@
        splice_tp @@
        Splice.foreign_tp univ @@ fun univ ->
        Splice.term @@ TB.pi TB.tp_dim @@ fun _ -> univ
      in
      let* _ = equate_con famtp fam0 fam1 in
      let* bdry_tp =
        lift_cmp @@ splice_tp @@
        Splice.foreign fam0 @@ fun fam ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        let phi = TB.boundary i in
        TB.pi (TB.tp_prf phi) @@ fun prf ->
        TB.el @@ TB.ap fam [i]
      in
      equate_con bdry_tp bdry0 bdry1

    | _ ->
      Format.eprintf "bad! equate_con!@.";
      throw @@ NbeFailed "unequal values"

  (* Invariant: cut0, cut1 are whnf *)
  and equate_cut cut0 cut1 =
    QuM.abort_if_inconsistent () @@
    let* () = assert_done_cut cut0 in
    let* () = assert_done_cut cut1 in
    let hd0, sp0 = cut0 in
    let hd1, sp1 = cut1 in
    match hd0, hd1 with
    | D.Split (tp, phi0, phi1, _, _), _
    | _, D.Split (tp, phi0, phi1, _, _) ->
      QuM.left_invert_under_cof (Cof.join phi0 phi1) @@
      let* con0 = contractum_or (D.Cut {tp; cut = cut0}) <@> lift_cmp @@ whnf_cut cut0 in
      let* con1 = contractum_or (D.Cut {tp; cut = cut1}) <@> lift_cmp @@ whnf_cut cut1 in
      equate_con tp con0 con1
    | _ ->
      let* () = equate_hd hd0 hd1 in
      equate_spine sp0 sp1

  (* Invariant: sp0, sp1 are whnf *)
  and equate_spine sp0 sp1 =
    match sp0, sp1 with
    | [], [] -> ret ()
    | k0 :: sp0, k1 :: sp1 ->
      let* () = equate_frm k0 k1 in
      equate_spine sp0 sp1
    | _ ->
      Format.eprintf "bad! equate_spine!.";
      throw @@ NbeFailed "Spine length mismatch"

  (* Invariant: k0, k1 are whnf *)
  and equate_frm k0 k1 =
    match k0, k1 with
    | D.KFst, D.KFst
    | D.KSnd, D.KSnd ->
      ret ()
    | D.KAp (tp0, con0), D.KAp (tp1, con1) ->
      let* () = equate_tp tp0 tp1 in
      equate_con tp0 con0 con1
    | D.KNatElim (mot0, zero_case0, suc_case0), D.KNatElim (mot1, zero_case1, suc_case1) ->
      let* fibx =
        bind_var D.TpAbort D.Nat @@ fun var ->
        let* fib0 = lift_cmp @@ inst_tp_clo mot0 [var] in
        let* fib1 = lift_cmp @@ inst_tp_clo mot1 [var] in
        let+ () = equate_tp fib0 fib1  in
        fib0
      in
      let* () =
        let* fib = lift_cmp @@ inst_tp_clo mot0 [D.Zero] in
        equate_con fib zero_case0 zero_case1
      in
      bind_var () D.Nat @@ fun x ->
      bind_var () fibx @@ fun ih ->
      let* fib_sucx = lift_cmp @@ inst_tp_clo mot0 [D.Suc x] in
      let* con0 = lift_cmp @@ inst_tm_clo suc_case0 [x; ih] in
      let* con1 = lift_cmp @@ inst_tm_clo suc_case1 [x; ih] in
      equate_con fib_sucx con0 con1
    | (D.KGoalProj, D.KGoalProj) ->
      ret ()
    | _ ->
      Format.eprintf "bad! equate_frame!@.";
      throw @@ NbeFailed "Mismatched frames"

  and assert_done_hd hd =
    let* w = lift_cmp @@ whnf_hd hd in
    match w with
    | `Done -> ret ()
    | _ -> failwith "internal error: assert_done_hd failed"

  and assert_done_cut cut =
    let* w = lift_cmp @@ whnf_cut cut in
    match w with
    | `Done -> ret ()
    | _ -> failwith "internal error: assert_done_cut failed"

  (* Invariant: hd0, hd1 are whnf *)
  and equate_hd hd0 hd1 =
    QuM.abort_if_inconsistent () @@
    let* () = assert_done_hd hd0 in
    let* () = assert_done_hd hd1 in
    match hd0, hd1 with
    | D.Global sym0, D.Global sym1 ->
      if Symbol.equal sym0 sym1 then ret () else
        throw @@ NbeFailed "Different head symbols"
    | D.Var lvl0, D.Var lvl1 ->
      if lvl0 = lvl1 then ret () else
        throw @@ NbeFailed "Different head variables"
    | D.Coe (abs0, r0, s0, con0), D.Coe (abs1, r1, s1, con1) ->
      let* () = equate_dim r0 r1 in
      let* () = equate_dim s0 s1 in
      let* () =
        bind_var_ D.TpDim @@ fun i ->
        let* code0 = lift_cmp @@ do_ap abs0 i in
        let* code1 = lift_cmp @@ do_ap abs1 i in
        equate_con D.Univ code0 code1
      in
      let* code = lift_cmp @@ do_ap abs0 @@ D.dim_to_con r0 in
      let* tp = lift_cmp @@ do_el code in
      equate_con tp con0 con1
    | D.HCom (cut0, r0, s0, phi0, bdy0), D.HCom (cut1, r1, s1, phi1, bdy1) ->
      let code0 = D.Cut {tp = D.Univ; cut = cut0} in
      let code1 = D.Cut {tp = D.Univ; cut = cut1} in
      equate_hcom (code0, r0, s0, phi0, bdy0) (code1, r1, s1, phi1, bdy1)
    | D.SubOut (cut0, _, _), D.SubOut (cut1, _, _) ->
      equate_cut cut0 cut1
    | hd, D.Split (tp, phi0, phi1, clo0, clo1)
    | D.Split (tp, phi0, phi1, clo0, clo1), hd ->
      let* () =
        QuM.left_invert_under_cof phi0 @@
        equate_con tp (D.Cut {tp; cut = hd,[]}) @<< lift_cmp @@ inst_tm_clo clo0 [D.Prf]
      in
      QuM.left_invert_under_cof phi1 @@
      equate_con tp (D.Cut {tp; cut = hd,[]}) @<< lift_cmp @@ inst_tm_clo clo1 [D.Prf]
    | _ ->
      Format.eprintf "bad! equate_hd : %a / %a@." D.pp_hd hd0 D.pp_hd hd1;
      throw @@ NbeFailed "Different heads"

  and equate_hcom (code0, r0, s0, phi0, bdy0) (code1, r1, s1, phi1, bdy1) =
    let* () = equate_con D.Univ code0 code1 in
    let* () = equate_dim r0 r1 in
    let* () = equate_dim s0 s1 in
    let* () = equate_cof phi0 phi1 in
    bind_var_ D.TpDim @@ fun i ->
    let* i_dim = lift_cmp @@ con_to_dim i in
    bind_var_ (D.TpPrf (Cof.join (Cof.eq i_dim r0) phi0)) @@ fun prf ->
    let* con0 = lift_cmp @@ do_ap2 bdy0 i prf in
    let* con1 = lift_cmp @@ do_ap2 bdy1 i prf in
    let* tp = lift_cmp @@ do_el code0 in
    equate_con tp con0 con1


  and equate_cof phi psi =
    let* () = approx_cof phi psi in
    approx_cof psi phi

  and approx_cof phi psi =
    CmpM.test_sequent [phi] psi |> lift_cmp |>> function
    | false ->
      throw @@ NbeFailed "Invalid cofibration sequent"
    | true ->
      ret ()

  let equal_tp tp0 tp1 : bool quote =
    successful @@
    QuM.left_invert_under_current_cof @@
    equate_tp tp0 tp1

  let equal_cut cut0 cut1 =
    successful @@
    QuM.left_invert_under_current_cof @@
    equate_cut cut0 cut1

  let equal_con tp con0 con1 =
    successful @@
    QuM.left_invert_under_current_cof @@
    equate_con tp con0 con1
end

include Quote