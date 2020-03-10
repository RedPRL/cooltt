(* This file implements the normalization procedure. In addition the "unary" quotation
 * algorithm described by the paper, we also implement a binary operation for increased
 * efficiency. *)
module S = Syntax
module D = Domain

open CoolBasis
open Bwd 
open BwdNotation
open Monads
open TLNat

exception NbeFailed of string

module rec Compute : 
sig 
  type 'a whnf = [`Done | `Reduce of 'a]
  val whnf_con : D.con -> D.con whnf compute
  val whnf_cut : D.cut -> D.con whnf compute
  val whnf_tp : D.tp -> D.tp whnf compute

  val inst_tp_clo : 'n D.tp_clo -> ('n, D.con) Vec.vec -> D.tp compute
  val inst_tm_clo : 'n D.tm_clo -> ('n, D.con) Vec.vec -> D.con compute
  val inst_tp_line_clo : S.tp D.line_clo -> D.dim -> D.tp compute
  val inst_line_clo : S.t D.line_clo -> D.dim -> D.con compute
  val inst_pline_clo : S.t D.pline_clo -> D.dim -> D.con compute
  val inst_pclo : S.t D.pclo -> D.con compute

  val do_nat_elim : ghost:D.ghost option -> ze su D.tp_clo -> D.con -> ze su su D.tm_clo -> D.con -> D.con compute
  val do_fst : D.con -> D.con compute
  val do_snd : D.con -> D.con compute
  val do_ap : D.con -> D.con -> D.con compute
  val do_sub_out : D.con -> D.con compute
  val do_id_elim : ghost:D.ghost option -> ze su su su D.tp_clo -> ze su D.tm_clo -> D.con -> D.con compute
  val do_goal_proj : D.con -> D.con compute
  val do_frm : D.con -> D.frm -> D.con compute
  val do_spine : D.con -> D.frm list -> D.con compute
  val do_el : D.con -> D.tp compute
  val force_lazy_con : D.lazy_con -> D.con compute

  val do_rigid_coe : D.coe_abs -> D.dim -> D.dim -> D.con -> D.con compute
  val do_rigid_hcom : D.con -> D.dim -> D.dim -> D.cof -> S.t D.pline_clo -> D.con compute
end =
struct
  open CmpM
  open Eval
  open Monad.Notation (CmpM)

  let dest_pi_code con = 
    match con with 
    | D.TpCode (D.Pi (base, fam)) ->
      ret (base, fam)
    | _ ->
      throw @@ NbeFailed "Expected pi code"

  let dest_sg_code con = 
    match con with 
    | D.TpCode (D.Sg (base, fam)) ->
      ret (base, fam)
    | _ ->
      throw @@ NbeFailed "Expected pi code"

  type 'a whnf = [`Done | `Reduce of 'a]

  let rec whnf_con : D.con -> D.con whnf m =
    function
    | D.Lam _ | D.Zero | D.Suc _ | D.Pair _ | D.Refl _ | D.GoalRet _ | D.TpCode _ | D.Abort | D.SubIn _ | D.Cof _ | D.DimCon0 | D.DimCon1 | D.Prf ->
      ret `Done

    | D.Cut {unfold = Some lcon} -> 
      reduce_to @<< force_lazy_con lcon

    | D.Cut {unfold = None; cut} ->
      whnf_cut cut

    | D.ConCoe (abs, r, s, con) ->
      begin
        test_sequent [] (Cof.eq r s) |>> function
        | true -> reduce_to con 
        | false -> ret `Done
      end

    | D.ConHCom (_, r, s, phi, clo) ->
      begin
        test_sequent [] (Cof.join (Cof.eq r s) phi) |>> function
        | true -> reduce_to @<< inst_pline_clo clo s
        | false -> ret `Done
      end

  and reduce_to con =
    whnf_con con |>> function
    | `Done -> ret @@ `Reduce con
    | `Reduce con -> ret @@ `Reduce con

  and whnf_cut cut : D.con whnf m =
    let hd, sp = cut in
    match hd with
    | D.Global _ | D.Var _ -> 
      ret `Done
    | D.Coe (abs, r, s, con) -> 
      begin
        test_sequent [] (Cof.eq r s) |>> function
        | true -> 
          reduce_to con 
        | false ->
          (* TODO, improve *)
          let+ coe = do_rigid_coe abs r s con in 
          `Reduce coe
      end
    | D.HCom (cut, r, s, phi, clo) ->
      begin
        Cof.join (Cof.eq r s) phi |> test_sequent [] |>> function
        | true ->
          let+ con = inst_pline_clo clo s in
          `Reduce con
        | false -> 
          whnf_cut cut |>> function
          | `Done -> 
            ret `Done
          | `Reduce code ->
            let+ hcom = do_rigid_hcom code r s phi clo in 
            `Reduce hcom
      end
    | D.SubOut (cut, phi, clo) ->
      begin
        test_sequent [] phi |>> function
        | true -> 
          let+ con = inst_pclo clo in
          `Reduce con
        | false ->
          whnf_cut cut |>> function
          | `Done ->
            ret `Done
          | `Reduce con ->
            let+ out = do_sub_out con in
            `Reduce out
      end

  and whnf_tp = 
    function
    | D.Tp (D.El cut) ->
      begin
        whnf_cut cut |>> function
        | `Done -> ret `Done
        | `Reduce con -> 
          let+ tp = do_el con  in
          `Reduce tp
      end
    | tp -> 
      ret `Done

  and do_nat_elim ~ghost (mot : ze su D.tp_clo) zero suc n : D.con compute =
    match n with
    | D.Zero -> 
      ret zero
    | D.Suc n -> 
      let* v = do_nat_elim ~ghost mot zero suc n in 
      inst_tm_clo suc [n; v]
    | D.Cut {cut; unfold} ->
      let+ fib = inst_tp_clo mot [n] in
      cut_frm ~tp:fib ~cut ~unfold @@
      D.KNatElim (ghost, mot, zero, suc) 
    | _ ->
      CmpM.throw @@ NbeFailed "Not a number"

  and do_id_elim ~ghost mot refl eq =
    match eq with
    | D.Refl t -> inst_tm_clo refl [t]
    | D.Cut {tp = D.Tp (D.Id (tp, con0, con1)); cut; unfold} -> 
      let+ fib = inst_tp_clo mot [con0; con1; eq] in 
      cut_frm ~tp:fib ~cut ~unfold @@
      D.KIdElim (ghost, mot, refl, tp, con0, con1)
    | _ -> 
      CmpM.throw @@ NbeFailed "Not a refl or neutral in do_id_elim"

  and cut_frm ~tp ~cut ~unfold frm = 
    let unfold = 
      unfold |> Option.map @@ 
      function 
      | `Done con ->
        `Do (con, [frm])
      | `Do (con, spine) -> 
        `Do (con, spine @ [frm])
    in
    D.Cut {tp; cut = D.push frm cut; unfold}

  and inst_tp_clo : type n. n D.tp_clo -> (n, D.con) Vec.vec -> D.tp compute =
    fun clo xs ->
    match clo with
    | Clo {bdy; env; _} -> 
      lift_ev (env <>< Vec.to_list xs) @@ 
      eval_tp bdy
    | ElClo clo ->
      let* con = inst_tm_clo clo xs in
      do_el con

  and inst_tm_clo : type n. n D.tm_clo -> (n, D.con) Vec.vec -> D.con compute =
    fun clo xs ->
    match clo with
    | D.Clo {bdy; env} -> 
      lift_ev (env <>< Vec.to_list xs) @@ 
      eval bdy

  and inst_tp_line_clo : S.tp D.line_clo -> D.dim -> D.tp compute = 
    fun clo r ->
    match clo with
    | D.LineClo (bdy, env) ->
      lift_ev (env <>< [D.dim_to_con r]) @@ eval_tp bdy

  and inst_line_clo : S.t D.line_clo -> D.dim -> D.con compute = 
    fun clo r ->
    match clo with 
    | D.LineClo (bdy, env) ->
      lift_ev (env <>< [D.dim_to_con r]) @@ eval bdy
    | D.PiCoeBaseClo clo -> 
      let* pi_code = inst_line_clo clo r in
      let+ base, _ = dest_pi_code pi_code in
      base
    | D.SgCoeBaseClo clo -> 
      let* sg_code = inst_line_clo clo r in
      let+ base, _ = dest_pi_code sg_code in
      base
    | D.PiCoeFibClo clo -> 
      let* base, fam = dest_pi_code @<< inst_line_clo clo.clo r in
      let* arg_r = do_coe clo.dest r clo.base_abs clo.arg in
      inst_tm_clo fam [arg_r]
    | D.SgCoeFibClo clo ->
      let* base, fam = dest_sg_code @<< inst_line_clo clo.clo r in
      let* fst_r = do_coe clo.src r clo.base_abs clo.fst in
      inst_tm_clo fam [fst_r]
    | D.SgHComFibClo clo ->
      let* fst_r = do_rigid_hcom clo.base clo.src r clo.cof @@ D.FstClo clo.clo in
      inst_tm_clo clo.fam [fst_r]

  and inst_pline_clo : S.t D.pline_clo -> D.dim -> D.con compute =
    fun clo r ->
    match clo with
    | D.PLineClo (bdy, env) -> 
      lift_ev (env <>< [D.dim_to_con r; D.Prf]) @@ eval bdy
    | D.AppClo (arg, clo) ->
      let* con = inst_pline_clo clo r in 
      do_ap con arg
    | D.FstClo clo -> 
      do_fst @<< inst_pline_clo clo r
    | D.SndClo clo -> 
      do_snd @<< inst_pline_clo clo r
    | D.ComClo (s, coe_abs, clo) ->
      let* con = inst_pline_clo clo r in
      do_rigid_coe coe_abs r s con

  and inst_pclo : S.t D.pclo -> D.con compute =
    function
    | D.PClo (bdy, env) ->
      lift_ev (env <>< [D.Prf]) @@ eval bdy
    | D.PCloConst con ->
      ret con

  and do_goal_proj =
    function
    | D.GoalRet con -> ret con
    | D.Cut {tp = D.Tp (D.GoalTp (_, tp)); cut; unfold} ->
      ret @@ cut_frm ~tp ~cut ~unfold D.KGoalProj
    | _ ->
      CmpM.throw @@ NbeFailed "do_goal_proj"

  and do_fst con : D.con compute =
    match con with
    | D.Pair (con0, _) -> 
      ret con0

    | D.ConCoe (D.CoeAbs abs, r, s, con) -> 
      let base_abs = D.CoeAbs {clo = D.SgCoeBaseClo abs.clo} in
      do_rigid_coe base_abs r s @<< do_fst con

    | D.ConHCom (code, r, s, phi, clo) -> 
      let* base, _ = dest_sg_code code in
      do_rigid_hcom base r s phi @@ D.FstClo clo

    | D.Cut {tp = D.Tp (D.Sg (base, _)); cut; unfold} ->
      ret @@ cut_frm ~tp:base ~cut ~unfold D.KFst

    | _ -> 
      throw @@ NbeFailed "Couldn't fst argument in do_fst"

  and do_snd con : D.con compute =
    match con with
    | D.Pair (_, con1) -> 
      ret con1

    | D.ConCoe (D.CoeAbs abs, r, s, con) -> 
      let base_abs = D.CoeAbs {clo = D.SgCoeBaseClo abs.clo} in
      let* con_fst = do_fst con in
      let fib_abs = D.CoeAbs {clo = D.SgCoeFibClo {src = r; base_abs; fst = con_fst; clo = abs.clo}} in
      do_rigid_coe fib_abs r s @<< do_snd con

    | D.ConHCom (code, r, s, phi, clo) -> 
      let* base, fam = dest_sg_code code in
      let* fib_abs = ret @@ D.CoeAbs {clo = SgHComFibClo {src = r; base; fam; cof = phi; clo}} in
      do_rigid_com fib_abs r s phi @@ D.SndClo clo

    | D.Cut {tp = D.Tp (D.Sg (_, fam)); cut; unfold} ->
      let* fst = do_fst con in
      let+ fib = inst_tp_clo fam [fst] in 
      cut_frm ~tp:fib ~cut ~unfold D.KSnd

    | _ -> 
      throw @@ NbeFailed ("Couldn't snd argument in do_snd")

  and do_ap f a =
    match f with
    | D.Lam clo -> 
      inst_tm_clo clo [a]

    | D.ConCoe (D.CoeAbs abs, r, s, f) ->
      let base_abs = D.CoeAbs {clo = D.PiCoeBaseClo abs.clo} in
      let fib_abs = D.CoeAbs {clo = D.PiCoeFibClo {dest = s; base_abs; arg = a; clo = abs.clo}} in
      do_rigid_coe fib_abs r s @<< do_ap f @<< do_rigid_coe base_abs s r a

    | D.ConHCom (code, r, s, phi, clo) ->
      let* base, fam = dest_pi_code code in
      let* fib = inst_tm_clo fam [a] in
      do_rigid_hcom fib r s phi @@ D.AppClo (a, clo)

    | D.Cut {tp = D.Tp (D.Pi (base, fam)); cut; unfold} ->
      let+ fib = inst_tp_clo fam [a] in
      cut_frm ~tp:fib ~cut ~unfold @@ D.KAp (base, a) 

    | _ -> 
      throw @@ NbeFailed "Not a function in do_ap"

  and do_sub_out v =
    match v with 
    | D.SubIn con ->
      ret con
    | D.Cut {tp = D.Tp (D.Sub (tp, phi, clo)); cut; unfold} ->
      ret @@ D.Cut {tp; cut = D.SubOut (cut, phi, clo), []; unfold = None} (* unfold ?? *)
    | _ ->
      throw @@ NbeFailed "do_sub_out"

  and do_el =
    function
    | D.Cut {cut; unfold = None} ->
      ret @@ D.Tp (D.El cut)

    | D.Cut {unfold = Some lcon} ->
      do_el @<< force_lazy_con lcon

    | D.TpCode D.Nat ->
      ret @@ D.Tp D.Nat

    | D.TpCode (D.Pi (base, clfam)) ->
      let+ base = do_el base in
      let clfam = D.ElClo clfam in
      D.Tp (D.Pi (base, clfam))

    | D.TpCode (D.Sg (base, clfam)) ->
      let+ base = do_el base in
      let clfam = D.ElClo clfam in
      D.Tp (D.Sg (base, clfam))

    | _ ->
      CmpM.throw @@ NbeFailed "do_el failed"

  and do_coe r s abs con =
    test_sequent [] (Cof.eq r s) |>> function
    | true -> ret con 
    | _ -> do_rigid_coe abs r s con

  and do_rigid_coe (D.CoeAbs abs) r s con =
    let i = D.DimProbe (Symbol.fresh ()) in
    let rec go peek =
      match peek with
      | D.TpCode (D.Pi _ | D.Sg _) ->
        ret @@ D.ConCoe (D.CoeAbs abs, r, s, con)
      | D.Cut {unfold = Some lcon} -> 
        go @<< force_lazy_con lcon
      | D.Cut {cut; unfold = None} ->
        let hd = D.Coe (D.CoeAbs abs, r, s, con) in
        let+ tp = do_el @<< inst_line_clo abs.clo s in
        D.Cut {tp; cut = hd, []; unfold = None}
      | _ ->
        throw @@ NbeFailed "Invalid arguments to do_rigid_coe"
    in
    go @<< inst_line_clo abs.clo i


  and do_rigid_hcom code r s phi clo = 
    match code with 
    | D.TpCode (D.Pi _ | D.Sg _)->
      ret @@ D.ConHCom (code, r, s, phi, clo)
    | D.Cut {unfold = Some lcon} ->
      let* code = force_lazy_con lcon in 
      do_rigid_hcom code r s phi clo
    | D.Cut {cut; unfold = None} ->
      let tp = D.Tp (D.El cut) in
      let hd = D.HCom (cut, r, s, phi, clo) in
      ret @@ D.Cut {tp; cut = hd, []; unfold = None}
    | _ ->
      throw @@ NbeFailed "Invalid arguments to do_rigid_hcom"

  and do_rigid_com (D.CoeAbs abs) r s phi clo =
    let* code_s = inst_line_clo abs.clo s in
    do_rigid_hcom code_s r s phi @@ D.ComClo (s, D.CoeAbs abs, clo)

  and force_lazy_con lcon : D.con m = 
    match lcon with 
    | `Done con -> ret con
    | `Do (con, spine) -> 
      do_spine con spine 

  and do_frm con =
    function
    | D.KAp (_, con') -> do_ap con con'
    | D.KFst -> do_fst con
    | D.KSnd -> do_snd con
    | D.KNatElim (ghost, mot, case_zero, case_suc) -> do_nat_elim ~ghost mot case_zero case_suc con
    | D.KIdElim (ghost, mot, case_refl, _, _, _) -> do_id_elim ~ghost mot case_refl con
    | D.KGoalProj -> do_goal_proj con

  and do_spine con =
    function
    | [] -> ret con
    | k :: sp ->
      let* con' = do_frm con k in
      do_spine con' sp
end

and Eval :
sig
  val eval : S.t -> D.con evaluate
  val eval_cof : S.t -> D.cof evaluate
  val eval_tp : S.tp -> D.tp evaluate
end = 
struct 
  open EvM
  open Compute
  open Monad.Notation (EvM)

  let get_local i =
    let* env = EvM.read_local in
    match Bwd.nth env i with 
    | v -> EvM.ret v 
    | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

  let rec eval_tp (S.Tp t) =
    match t with
    | S.Nat -> ret @@ D.Tp (D.Nat)
    | S.Pi (base, fam) -> 
      let+ vbase = eval_tp base 
      and+ clfam = close_tp fam in
      D.Tp (D.Pi (vbase, clfam))
    | S.Sg (base, fam) -> 
      let+ vbase = eval_tp base 
      and+ clfam = close_tp fam in
      D.Tp (D.Sg (vbase, clfam))
    | S.Id (tp, left, right) ->
      let+ vtp = eval_tp tp
      and+ vl = eval left 
      and+ vr = eval right in
      D.Tp (D.Id (vtp, vl, vr))
    | S.Univ ->
      ret @@ D.Tp D.Univ
    | S.El tm ->
      let* con = eval tm in
      lift_cmp @@ do_el con
    | S.GoalTp (lbl, tp) ->
      let+ tp = eval_tp tp in
      D.Tp (D.GoalTp (lbl, tp))
    | S.Sub (tp, tphi, tm) ->
      let+ env = read_local 
      and+ tp = eval_tp tp 
      and+ phi = con_to_cof @<< eval tphi in
      let cl = D.PClo (tm, env) in
      D.Tp (D.Sub (tp, phi, cl))
    | S.TpDim  ->
      ret @@ D.Tp D.TpDim
    | S.TpCof -> 
      ret @@ D.Tp D.TpCof
    | S.TpPrf tphi ->
      let+ phi = con_to_cof @<< eval tphi in 
      D.Tp (D.TpPrf phi)

  and eval =
    function
    | S.Var i -> get_local i
    | S.Global sym -> 
      let* st = EvM.read_global in
      let tp, con = ElabState.get_global sym st in
      ret @@ D.Cut {tp; cut = (D.Global sym, []); unfold = Some (`Done con)}
    | S.Let (def, body) -> 
      let* vdef = eval def in 
      append [vdef] @@ eval body
    | S.Ann (term, _) -> 
      eval term
    | S.Zero -> 
      ret D.Zero
    | S.Suc t -> 
      let+ con = eval t in
      D.Suc con
    | S.NatElim (ghost, tp, zero, suc, n) ->
      let* vzero = eval zero in
      let* vn = eval n in
      let* cltp = EvM.close_tp tp in
      let* clsuc = close_tm suc in
      let* ghost = eval_ghost ghost in
      lift_cmp @@ do_nat_elim ~ghost cltp vzero clsuc vn
    | S.Lam t -> 
      let+ cl = close_tm t in
      D.Lam cl
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
    | S.Refl t -> 
      let+ con = eval t in
      D.Refl con
    | S.IdElim (ghost, mot, refl, eq) ->
      let* veq = eval eq in 
      let* clmot = close_tp mot in
      let* clrefl = close_tm refl in
      let* ghost = eval_ghost ghost in
      lift_cmp @@ do_id_elim ~ghost clmot clrefl veq
    | S.GoalRet tm ->
      let+ con = eval tm in
      D.GoalRet con
    | S.GoalProj tm ->
      let* con = eval tm in
      lift_cmp @@ do_goal_proj con
    | S.TpCode tm ->
      let+ vcode = eval_tp_code tm in
      D.TpCode vcode
    | S.Coe (tpcode, tr, ts, tm) ->
      let* r = eval_dim tr in
      let* s = eval_dim ts in
      let* con = eval tm in
      begin
        CmpM.test_sequent [] (Cof.eq r s) |> lift_cmp |>> function
        | true -> 
          ret con
        | false -> 
          let* coe_abs = eval_coe_abs tpcode in
          lift_cmp @@ do_rigid_coe coe_abs r s con
      end
    | S.HCom (tpcode, tr, ts, tphi, tm) ->
      let* r = eval_dim tr in
      let* s = eval_dim ts in
      let* phi = con_to_cof @<< eval tphi in
      let* vtpcode = eval tpcode in
      begin
        CmpM.test_sequent [] (Cof.join (Cof.eq r s) phi) |> lift_cmp |>> function
        | true -> 
          append [D.dim_to_con s] @@ eval tm
        | false ->
          let* env = read_local in
          let clo = D.PLineClo (tm, env) in
          lift_cmp @@ do_rigid_hcom vtpcode r s phi clo
      end
    | S.CofTree tree -> 
      force_eval_cof_tree tree
    | S.SubOut tm ->
      let* con = eval tm in
      lift_cmp @@ Compute.do_sub_out con
    | S.SubIn t -> 
      let+ con = eval t in
      D.SubIn con
    | S.Dim0 -> ret D.DimCon0
    | S.Dim1 -> ret D.DimCon1
    | S.Cof cof_f ->
      begin
        match cof_f with
        | Cof.Eq (tr, ts) ->
          let+ r = eval tr 
          and+ s = eval ts in
          D.Cof (Cof.Eq (r, s))
        | Cof.Top -> ret @@ D.Cof Cof.Top
        | Cof.Bot -> ret @@ D.Cof Cof.Bot
        | Cof.Join (tphi, tpsi) ->
          let+ phi = eval tphi 
          and+ psi = eval tpsi in 
          D.Cof (Cof.Join (phi, psi))
        | Cof.Meet (tphi, tpsi) ->
          let+ phi = eval tphi 
          and+ psi = eval tpsi in 
          D.Cof (Cof.Meet (phi, psi))
      end

  and con_to_dim =
    function
    | D.DimCon0 -> ret D.Dim0
    | D.DimCon1 -> ret D.Dim1
    | D.Cut {cut = Var l, []} -> ret @@ D.DimVar l
    | _ -> throw @@ NbeFailed "con_to_dim"

  and eval_dim tr =
    let* con = eval tr in
    con_to_dim con

  and force_eval_cof_tree tree =
    eval_cof_tree tree |>> function
    | `Valid con -> ret con
    | `Invalid -> 
      throw @@ NbeFailed "Cofibration not true in current environment"


  and eval_cof_tree =
    function
    | Cof.Const (tphi, tm) ->
      let* phi = con_to_cof @<< eval tphi in
      begin
        CmpM.test_sequent [] phi |> lift_cmp |>> function
        | true ->
          let+ con = eval tm in 
          `Valid con
        | false -> 
          ret `Invalid
      end 
    | Cof.Abort ->
      begin
        CmpM.test_sequent [] Cof.bot |> lift_cmp |>> function
        | true ->
          ret @@ `Valid D.Abort
        | false -> 
          ret `Invalid
      end
    | Cof.Split (tree0, tree1) -> 
      eval_cof_tree tree0 |>> function
      | `Valid con -> 
        ret @@ `Valid con
      | `Invalid -> 
        eval_cof_tree tree1

  and cof_con_to_cof : (D.con, D.con) Cof.cof_f -> (int, D.dim) Cof.cof m =
    function
    | Cof.Eq (r, s) ->
      let+ r = con_to_dim r 
      and+ s = con_to_dim s in
      Cof.eq r s
    | Cof.Join (phi, psi) -> 
      let+ phi = con_to_cof phi 
      and+ psi = con_to_cof psi in
      Cof.join phi psi
    | Cof.Meet (phi, psi) ->
      let+ phi = con_to_cof phi 
      and+ psi = con_to_cof psi in
      Cof.meet phi psi
    | Cof.Bot -> ret Cof.bot
    | Cof.Top -> ret Cof.top

  and con_to_cof = 
    function
    | Cof cof -> cof_con_to_cof cof
    | D.Cut {cut = D.Var l, []} -> ret @@ Cof.var l
    | _ -> throw @@ NbeFailed "con_to_cof"

  and eval_cof tphi = 
    con_to_cof @<< eval tphi

  and eval_coe_abs code = 
    let+ env = read_local in 
    let clo = D.LineClo (code, env) in
    D.CoeAbs {clo} 

  and eval_tp_code =
    function
    | S.Nat ->
      ret @@ D.Nat
    | S.Pi (base, fam) ->
      let+ vbase = eval base
      and+ clfam = close_tm fam in
      D.Pi (vbase, clfam)
    | S.Sg (base, fam) ->
      let+ vbase = eval base
      and+ clfam = close_tm fam in
      D.Sg (vbase, clfam)
    | S.Id (tp, left, right) ->
      let+ vtp = eval tp
      and+ vl = eval left 
      and+ vr = eval right in
      D.Id (vtp, vl, vr)
    | S.Sub (tp, tphi, tm) ->
      let+ env = read_local 
      and+ tp = eval tp 
      and+ phi = con_to_cof @<< eval tphi in
      let cl = D.PClo (tm, env) in
      D.Sub (tp, phi, cl)

  and eval_ghost =
    function 
    | None -> 
      ret None
    | Some (lbl, cells) ->
      let rec go =
        function 
        | [] -> 
          ret []
        | (tp, tm) :: cells -> 
          let+ tp = eval_tp tp 
          and+ con = eval tm
          and+ cells = go cells in
          (tp, con) :: cells
      in 
      let+ cells = go cells in
      Some (lbl, cells)
end

module Quote : sig 
  val quote_con : D.tp -> D.con -> S.t quote
  val quote_tp : D.tp -> S.tp quote
  val equal_con : D.tp -> D.con -> D.con -> bool quote
  val quote_cut : D.cut -> S.t quote
  val equal_tp : D.tp -> D.tp -> bool quote
  val equal_cut : D.cut -> D.cut -> bool quote
  val equate_con : D.tp -> D.con -> D.con -> unit quote
  val equate_tp : D.tp -> D.tp -> unit quote
  val equate_cut : D.cut -> D.cut -> unit quote
end = 
struct
  open QuM
  open Monad.Notation (QuM)
  open Compute

  let top_var tp =
    let+ n = read_local in 
    D.mk_var tp @@ n - 1

  let top_dim_var =
    let+ n = read_local in
    D.DimVar (n - 1)

  let rec quote_con (D.Tp tp) con : S.t m =
    match tp, con with 
    | _, D.Cut {cut = (hd, sp); unfold; tp} ->
      begin
        match hd, unfold with
        | D.Global sym, Some lcon ->
          let* veil = read_veil in
          begin
            match Veil.policy sym veil with
            | `Transparent ->
              quote_con tp @<< 
              lift_cmp @@ force_lazy_con lcon 
            | _ ->
              quote_cut (hd, sp)
          end
        | _ -> 
          quote_cut (hd, sp)
      end
    | D.Pi (base, fam), con ->
      binder 1 @@ 
      let* arg = top_var base in
      let* fib = lift_cmp @@ inst_tp_clo fam [arg] in
      let* ap = lift_cmp @@ do_ap con arg in
      let+ body = quote_con fib ap in
      S.Lam body
    | D.Sg (base, fam), _ ->
      let* fst = lift_cmp @@ do_fst con in
      let* snd = lift_cmp @@ do_snd con in
      let* fib = lift_cmp @@ inst_tp_clo fam [fst] in 
      let+ tfst = quote_con base fst
      and+ tsnd = quote_con fib snd in 
      S.Pair (tfst, tsnd)
    | D.Nat, D.Zero ->
      ret S.Zero
    | D.Nat, D.Suc n ->
      let+ tn = quote_con (D.Tp D.Nat) n in 
      S.Suc tn
    | D.Id (tp, _, _), D.Refl con ->
      let+ t = quote_con tp con in 
      S.Refl t
    | D.Univ, D.TpCode code ->
      let+ tcode = quote_tp_code (D.Tp D.Univ) code in
      S.TpCode tcode
    | _ -> 
      throw @@ NbeFailed "ill-typed quotation problem"

  and quote_tp_code univ =
    function
    | D.Nat -> 
      ret S.Nat
    | D.Pi (base, fam) ->
      let+ tbase = quote_con univ base 
      and+ tfam = 
        let* tpbase = lift_cmp @@ do_el base in
        binder 1 @@
        let* var = top_var tpbase in
        quote_con univ @<< 
        lift_cmp @@ inst_tm_clo fam [var] 
      in 
      S.Pi (tbase, tfam)
    | D.Sg (base, fam) ->
      let+ tbase = quote_con (D.Tp D.Univ) base 
      and+ tfam = 
        let* tpbase = lift_cmp @@ do_el base in
        binder 1 @@
        let* var = top_var tpbase in
        quote_con univ @<< 
        lift_cmp @@ inst_tm_clo fam [var] 
      in 
      S.Sg (tbase, tfam)
    | D.Id (tp, left, right) ->
      let* eltp = lift_cmp @@ do_el tp in
      let+ ttp = quote_con univ tp 
      and+ tleft = quote_con eltp left 
      and+ tright = quote_con eltp right in 
      S.Id (ttp, tleft, tright)
    | D.Sub (tp, phi, cl) ->
      let* eltp = lift_cmp @@ do_el tp in
      let* ttp = quote_con univ tp in
      let* tphi = quote_cof phi in
      let+ tree = 
        quote_cof_tree @<<
        under_cofs [phi] @@ 
        quote_con eltp @<< lift_cmp @@ inst_pclo cl
      in
      S.Sub (ttp, tphi, S.CofTree tree)

  and quote_tp (D.Tp tp) =
    match tp with
    | D.Nat -> ret @@ S.Tp S.Nat
    | D.Pi (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        binder 1 @@ 
        let* var = top_var base in
        quote_tp @<< 
        lift_cmp @@ inst_tp_clo fam [var] 
      in
      S.Tp (S.Pi (tbase, tfam))
    | D.Sg (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        binder 1 @@ 
        let* var = top_var base in
        quote_tp @<< 
        lift_cmp @@ inst_tp_clo fam [var]
      in
      S.Tp (S.Sg (tbase, tfam))
    | D.Id (tp, left, right) ->
      let+ ttp = quote_tp tp 
      and+ tleft = quote_con tp left 
      and+ tright = quote_con tp right in 
      S.Tp (S.Id (ttp, tleft, tright))
    | D.Univ ->
      ret @@ S.Tp S.Univ
    | D.El cut ->
      let+ tm = quote_cut cut in
      S.Tp (S.El tm)
    | D.GoalTp (lbl, tp) ->
      let+ tp = quote_tp tp in
      S.Tp (S.GoalTp (lbl, tp))
    | D.Sub (tp, phi, cl) ->
      let* ttp = quote_tp tp in
      let* tphi = quote_cof phi in
      let+ tree = 
        quote_cof_tree @<<
        under_cofs [phi] @@ 
        quote_con tp @<< lift_cmp @@ inst_pclo cl
      in
      S.Tp (S.Sub (ttp, tphi, S.CofTree tree))
    | D.TpDim -> 
      ret @@ S.Tp S.TpDim
    | D.TpCof -> 
      ret @@ S.Tp S.TpCof
    | D.TpPrf phi ->
      let+ tphi = quote_cof phi in 
      S.Tp (S.TpPrf tphi)


  and quote_hd =
    function
    | D.Var lvl -> 
      let+ n = read_local in 
      S.Var (n - (lvl + 1))
    | D.Global sym ->
      ret @@ S.Global sym
    | D.Coe (D.CoeAbs abs, r, s, con) ->
      let* tpcode = 
        binder 1 @@ 
        let* i = top_dim_var in
        let* code = lift_cmp @@ inst_line_clo abs.clo i in
        quote_con (D.Tp D.Univ) code
      in
      let* tr = quote_dim r in
      let* ts = quote_dim s in
      let* tp_con_r = lift_cmp @@ inst_line_clo abs.clo r in
      let* tp_r = lift_cmp @@ do_el tp_con_r in
      let+ tm = quote_con tp_r con in
      S.Coe (tpcode, tr, ts, tm)
    | D.HCom (cut, r, s, phi, clo) ->
      let* tpcode = quote_cut cut in
      let* tr = quote_dim r in
      let* ts = quote_dim s in
      let* tphi = quote_cof phi in
      let+ tube = 
        binder 1 @@ 
        let* i = top_dim_var in
        let+ tree = 
          quote_cof_tree @<<
          under_cofs [Cof.join (Cof.eq r i) phi] @@
          let* body = lift_cmp @@ inst_pline_clo clo i in 
          quote_con (D.Tp (D.El cut)) body
        in
        S.CofTree tree
      in
      S.HCom (tpcode, tr, ts, tphi, tube)
    | D.SubOut (cut, phi, clo) ->
      let+ tm = quote_cut cut in
      S.SubOut tm

  and quote_cof_tree = 
    function 
    | Cof.Const (phi, tm) -> 
      let+ tphi = quote_cof phi in 
      Cof.const (tphi, tm)
    | Cof.Split (tree0, tree1) ->
      let+ ttree0 = quote_cof_tree tree0 
      and+ ttree1 = quote_cof_tree tree1 in
      Cof.split ttree0 ttree1
    | Cof.Abort ->
      ret Cof.abort

  and quote_dim =
    function
    | D.Dim0 -> ret S.Dim0 
    | D.Dim1 -> ret S.Dim1
    | D.DimVar lvl -> 
      let+ ix = quote_var lvl in
      S.Var ix
    | D.DimProbe _ -> 
      failwith "DimProbe should not be quoted!"

  and quote_cof =
    function
    | Cof.Var lvl ->
      let+ ix = quote_var lvl in
      S.Var ix
    | Cof.Cof phi ->
      match phi with
      | Cof.Eq (r, s) ->
        let+ tr = quote_con (D.Tp D.TpDim) @@ D.dim_to_con r 
        and+ ts = quote_con (D.Tp D.TpDim) @@ D.dim_to_con s in
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

  and quote_ghost =
    function
    | None -> ret None
    | Some (lbl, cells) -> 
      let rec go =
        function
        | [] -> ret []
        | (tp, con) :: cells ->
          let+ ttp = quote_tp tp 
          and+ tm = quote_con tp con 
          and+ cells = go cells in
          (ttp, tm) :: cells
      in
      let+ cells = go cells in
      Some (lbl, cells)

  and quote_frm tm = 
    function
    | D.KNatElim (ghost, mot, zero_case, suc_case) ->
      let* x, mot_x, tmot = 
        binder 1 @@ 
        let* x = top_var @@ D.Tp D.Nat in
        let* mot_x = lift_cmp @@ inst_tp_clo mot [x] in 
        let+ tmot = quote_tp mot_x in 
        x, mot_x, tmot
      in
      let+ tzero_case = 
        let* mot_zero = lift_cmp @@ inst_tp_clo mot [D.Zero] in
        quote_con mot_zero zero_case
      and+ tsuc_case =
        binder 2 @@
        let* ih = top_var mot_x in 
        let* mot_suc_x = lift_cmp @@ inst_tp_clo mot [D.Suc x] in 
        let* suc_case_x = lift_cmp @@ inst_tm_clo suc_case [x; ih] in
        quote_con mot_suc_x suc_case_x
      and+ ghost = quote_ghost ghost 
      in
      S.NatElim (ghost, tmot, tzero_case, tsuc_case, tm)
    | D.KIdElim (ghost, mot, refl_case, tp, left, right) ->
      let* x, tmot =
        binder 1 @@ 
        let* x = top_var tp in 
        binder 1 @@ 
        let* y = top_var tp in 
        binder 1 @@ 
        let* z = top_var @@ D.Tp (D.Id (tp, left, right)) in 
        let* mot_xyz = lift_cmp @@ inst_tp_clo mot [x; y; z] in
        let+ tmot = quote_tp mot_xyz in 
        x, tmot
      in 
      let+ trefl_case =
        binder 1 @@ 
        let* mot_refl_x = lift_cmp @@ inst_tp_clo mot [x; x; D.Refl x] in
        let* refl_case_x = lift_cmp @@ inst_tm_clo refl_case [x] in
        quote_con mot_refl_x refl_case_x
      and+ ghost = quote_ghost ghost 
      in
      S.IdElim (ghost, tmot, trefl_case, tm)
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

  let tp_proj (D.Tp tp) = 
    tp

  (* Invariant: tp0 and tp1 not necessarily whnf *)
  let rec equate_tp tp0 tp1 =
    let* tp0 = contractum_or tp0 <@> lift_cmp @@ whnf_tp tp0 in
    let* tp1 = contractum_or tp1 <@> lift_cmp @@ whnf_tp tp1 in
    match tp_proj tp0, tp_proj tp1 with
    | D.Pi (base0, fam0), D.Pi (base1, fam1) 
    | D.Sg (base0, fam0), D.Sg (base1, fam1) ->
      let* () = equate_tp base0 base1 in
      binder 1 @@ 
      let* x = top_var base0 in
      let* fib0 = lift_cmp @@ inst_tp_clo fam0 [x] in
      let* fib1 = lift_cmp @@ inst_tp_clo fam1 [x] in
      equate_tp fib0 fib1
    | D.Id (tp0, l0, r0), D.Id (tp1, l1, r1) ->
      let* () = equate_tp tp0 tp1 in
      let* () = equate_con tp0 l0 l1 in
      equate_con tp0 r0 r1
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
    let* tp = contractum_or tp <@> lift_cmp @@ whnf_tp tp in
    let* con0 = contractum_or con0 <@> lift_cmp @@ whnf_con con0 in
    let* con1 = contractum_or con1 <@> lift_cmp @@ whnf_con con1 in
    match tp_proj tp, con0, con1 with
    | D.Pi (base, fam), _, _ ->
      binder 1 @@ 
      let* x = top_var base in 
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
    | D.Sub _, _, _ ->
      failwith "todo: issue 28"
    | D.Id (tp, _, _), D.Refl x, D.Refl y ->
      equate_con tp x y
    | _, D.Zero, D.Zero ->
      ret ()
    | _, D.Suc con0, D.Suc con1 ->
      equate_con tp con0 con1
    | _, D.Cut {cut = cut0; unfold = None}, D.Cut {cut = cut1; unfold = None} ->
      equate_cut cut0 cut1
    | _, (D.TpCode _ as con0), (D.TpCode _ as con1) -> 
      let* tp0 = lift_cmp @@ do_el con0 in
      let* tp1 = lift_cmp @@ do_el con1 in
      equate_tp tp0 tp1
    | _ -> 
      throw @@ NbeFailed "unequal values"

  (* Invariant: cut0, cut1 are whnf *)
  and equate_cut cut0 cut1 = 
    let hd0, sp0 = cut0 in
    let hd1, sp1 = cut1 in
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
    | D.KNatElim (_, mot0, zero_case0, suc_case0), D.KNatElim (_, mot1, zero_case1, suc_case1) ->
      let* fibx =
        binder 1 @@
        let* var = top_var @@ D.Tp D.Nat in
        let* fib0 = lift_cmp @@ inst_tp_clo mot0 [var] in
        let* fib1 = lift_cmp @@ inst_tp_clo mot1 [var] in
        let+ () = equate_tp fib0 fib1  in
        fib0 
      in
      let* () = 
        let* fib = lift_cmp @@ inst_tp_clo mot0 [D.Zero] in
        equate_con fib zero_case0 zero_case1
      in
      binder 1 @@
      let* x = top_var @@ D.Tp D.Nat in 
      binder 1 @@ 
      let* ih = top_var fibx in
      let* fib_sucx = lift_cmp @@ inst_tp_clo mot0 [D.Suc x] in
      let* con0 = lift_cmp @@ inst_tm_clo suc_case0 [x; ih] in
      let* con1 = lift_cmp @@ inst_tm_clo suc_case1 [x; ih] in
      equate_con fib_sucx con0 con1
    | D.KIdElim (_, mot0, refl_case0, tp0, left0, right0), D.KIdElim (_, mot1, refl_case1, tp1, left1, right1) ->
      let* () = equate_tp tp0 tp1 in
      let* () = equate_con tp0 left0 left1 in
      let* () = equate_con tp0 right0 right1 in
      let* () =
        binder 1 @@
        let* l = top_var tp0 in
        binder 1 @@ 
        let* r = top_var tp0 in
        binder 1 @@ 
        let* p = top_var @@ D.Tp (D.Id (tp0, l, r)) in
        let* fib0 = lift_cmp @@ inst_tp_clo mot0 [l; r; p] in
        let* fib1 = lift_cmp @@ inst_tp_clo mot1 [l; r; p] in
        equate_tp fib0 fib1
      in
      binder 1 @@
      let* x = top_var tp0 in
      let* fib_reflx = lift_cmp @@ inst_tp_clo mot0 [x; x; D.Refl x] in
      let* con0 = lift_cmp @@ inst_tm_clo refl_case0 [x] in
      let* con1 = lift_cmp @@ inst_tm_clo refl_case1 [x] in
      equate_con fib_reflx con0 con1
    | (D.KGoalProj, D.KGoalProj) ->
      ret ()
    | _ -> 
      throw @@ NbeFailed "Mismatched frames"

  (* Invariant: hd0, hd1 are whnf *)
  and equate_hd hd0 hd1 = 
    match hd0, hd1 with
    | D.Global sym0, D.Global sym1 ->
      if Symbol.equal sym0 sym1 then ret () else 
        throw @@ NbeFailed "Different head symbols"
    | D.Var lvl0, D.Var lvl1 ->
      if lvl0 = lvl1 then ret () else
        throw @@ NbeFailed "Different head variables"
    | D.Coe (D.CoeAbs abs0, r0, s0, con0), D.Coe (D.CoeAbs abs1, r1, s1, con1) -> 
      let* () = equate_dim r0 r1 in
      let* () = equate_dim s0 s1 in
      let* () = 
        binder 1 @@ 
        let* i = top_dim_var in
        let* code0 = lift_cmp @@ inst_line_clo abs0.clo i in
        let* code1 = lift_cmp @@ inst_line_clo abs0.clo i in
        equate_con (D.Tp D.Univ) code0 code1
      in
      let* code = lift_cmp @@ inst_line_clo abs0.clo r0 in
      let* tp = lift_cmp @@ do_el code in
      equate_con tp con0 con1
    | D.HCom (cut0, r0, s0, phi0, clo0), D.HCom (cut1, r1, s1, phi1, clo1) ->
      let* () = equate_cut cut0 cut1 in
      let* () = equate_dim r0 r1 in
      let* () = equate_dim s0 s1 in
      let* () = approx_cof phi0 phi1 in
      let* () = approx_cof phi1 phi0 in
      binder 1 @@ 
      let* i = top_dim_var in
      under_cofs_ [Cof.join (Cof.eq i r0) phi0] @@ 
      let* con0 = lift_cmp @@ inst_pline_clo clo0 i in
      let* con1 = lift_cmp @@ inst_pline_clo clo1 i in
      let tp = D.Tp (D.El cut0) in
      equate_con tp con0 con1
    | D.SubOut (cut0, _, _), D.SubOut (cut1, _, _) ->
      equate_cut cut0 cut1
    | _ ->
      throw @@ NbeFailed "Different heads"

  and approx_cof phi psi =
    CmpM.test_sequent [phi] psi |> lift_cmp |>> function 
    | false ->
      throw @@ NbeFailed "Invalid cofibration sequent"
    | true ->
      ret ()

  let equal_tp tp0 tp1 : bool quote = 
    successful @@ equate_tp tp0 tp1

  let equal_cut cut0 cut1 = 
    successful @@ equate_cut cut0 cut1

  let equal_con tp con0 con1 = 
    successful @@ equate_con tp con0 con1
end

include Eval
include Quote
include Compute