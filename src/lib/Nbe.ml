module S = Syntax
module D = Domain


exception Todo

open CoolBasis
open Bwd 
open BwdNotation
open Monads

exception NbeFailed of string

module QQ = Quasiquote
module TB = TermBuilder


module rec Compute : 
sig 
  type 'a whnf = [`Done | `Reduce of 'a]
  val whnf_con : D.con -> D.con whnf compute
  val whnf_cut : D.cut -> D.con whnf compute
  val whnf_tp : D.tp -> D.tp whnf compute

  val inst_tp_clo : D.tp_clo -> D.con list -> D.tp compute
  val inst_tm_clo : D.tm_clo -> D.con list -> D.con compute

  val do_nat_elim : ghost:D.ghost option -> D.tp_clo -> D.con -> D.tm_clo -> D.con -> D.con compute
  val do_fst : D.con -> D.con compute
  val do_snd : D.con -> D.con compute
  val do_ap : D.con -> D.con -> D.con compute
  val do_ap2 : D.con -> D.con -> D.con -> D.con compute
  val do_sub_out : D.con -> D.con compute
  val do_id_elim : ghost:D.ghost option -> D.tp_clo -> D.tm_clo -> D.con -> D.con compute
  val do_goal_proj : D.con -> D.con compute
  val do_frm : D.con -> D.frm -> D.con compute
  val do_spine : D.con -> D.frm list -> D.con compute
  val do_el : D.con -> D.tp compute
  val force_lazy_con : D.lazy_con -> D.con compute

  val do_rigid_coe : D.con -> D.dim -> D.dim -> D.con -> D.con compute
  val do_rigid_hcom : D.con -> D.dim -> D.dim -> D.cof -> D.con -> D.con compute

  val con_to_dim : D.con -> D.dim compute
  val con_to_cof : D.con -> D.cof compute
  val cof_con_to_cof : (D.con, D.con) Cof.cof_f -> D.cof compute

  val quasiquote_tm : S.t QQ.builder -> D.con compute
  val quasiquote_tp : S.tp QQ.builder -> D.tp compute
end =
struct
  open CmpM
  open Eval
  open Monad.Notation (CmpM)

  let quasiquote_tm builder =
    let env, tm = QQ.compile builder in 
    lift_ev env @@ eval tm

  let quasiquote_tp builder = 
    let env, tp = QQ.compile builder in 
    lift_ev env @@ eval_tp tp


  let con_to_dim =
    function
    | D.DimCon0 -> ret D.Dim0
    | D.DimCon1 -> ret D.Dim1
    | D.Cut {cut = Var l, []} -> ret @@ D.DimVar l
    | con -> 
      Format.eprintf "bad: %a@." D.pp_con con;
      throw @@ NbeFailed "con_to_dim"

  let rec cof_con_to_cof : (D.con, D.con) Cof.cof_f -> D.cof m =
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


  let dest_pi_code con = 
    match con with 
    | D.CodePi (base, fam) ->
      ret (base, fam)
    | _ ->
      throw @@ NbeFailed "Expected pi code"

  let dest_sg_code con = 
    match con with 
    | D.CodeSg (base, fam) ->
      ret (base, fam)
    | _ ->
      throw @@ NbeFailed "Expected pi code"

  type 'a whnf = [`Done | `Reduce of 'a]

  let rec whnf_con : D.con -> D.con whnf m =
    function
    | D.Lam _ | D.Zero | D.Suc _ | D.Pair _ | D.Refl _ | D.GoalRet _ | D.Abort | D.SubIn _ 
    | D.Cof _ | D.DimCon0 | D.DimCon1 | D.Prf 
    | D.CodePath _ | CodePi _ | D.CodeSg _ | D.CodeNat 
    | D.Destruct _ ->
      ret `Done

    | D.Cut {unfold = Some lcon} -> 
      reduce_to @<< force_lazy_con lcon

    | D.Cut {unfold = None; cut} ->
      whnf_cut cut

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
          reduce_to @<< do_rigid_coe abs r s con 
      end
    | D.HCom (cut, r, s, phi, bdy) ->
      begin
        Cof.join (Cof.eq r s) phi |> test_sequent [] |>> function
        | true ->
          reduce_to @<< do_ap2 bdy (D.dim_to_con s) D.Prf 
        | false -> 
          whnf_cut cut |>> function
          | `Done -> 
            ret `Done
          | `Reduce code ->
            reduce_to @<< do_rigid_hcom code r s phi bdy 
      end
    | D.SubOut (cut, phi, clo) ->
      begin
        test_sequent [] phi |>> function
        | true -> 
          let+ con = inst_tm_clo clo [D.Prf] in
          `Reduce con
        | false ->
          whnf_cut cut |>> function
          | `Done ->
            ret `Done
          | `Reduce con ->
            reduce_to @<< do_sub_out con 
      end
    | D.Split (tp, phi0, phi1, clo0, clo1) ->
      begin
        test_sequent [] phi0 |>> function
        | true -> 
          reduce_to @<< inst_tm_clo clo0 [D.Prf] 
        | false ->
          test_sequent [] phi1 |>> function
          | true -> 
            reduce_to @<< inst_tm_clo clo1 [D.Prf] 
          | false -> 
            ret `Done
      end


  and whnf_tp = 
    function
    | D.El cut ->
      begin
        whnf_cut cut |>> function
        | `Done -> ret `Done
        | `Reduce con -> 
          let+ tp = do_el con  in
          `Reduce tp
      end
    | tp -> 
      ret `Done

  and do_nat_elim ~ghost (mot : D.tp_clo) zero suc n : D.con compute =
    match n with
    | D.Abort -> ret D.Abort
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
    | D.Abort -> ret D.Abort
    | D.Refl t -> inst_tm_clo refl [t]
    | D.Cut {tp = D.Id (tp, con0, con1); cut; unfold} -> 
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

  and inst_tp_clo : D.tp_clo -> D.con list -> D.tp compute =
    fun clo xs ->
    match clo with
    | TpClo (bdy, env) ->
      lift_ev {env with conenv = env.conenv <>< xs} @@ 
      eval_tp bdy

  and inst_tm_clo : D.tm_clo -> D.con list -> D.con compute =
    fun clo xs ->
    match clo with
    | D.Clo (bdy, env) -> 
      lift_ev {env with conenv = env.conenv <>< xs} @@ 
      eval bdy

  and do_goal_proj =
    function
    | D.Abort -> ret D.Abort
    | D.GoalRet con -> ret con
    | D.Cut {tp = D.GoalTp (_, tp); cut; unfold} ->
      ret @@ cut_frm ~tp ~cut ~unfold D.KGoalProj
    | _ ->
      CmpM.throw @@ NbeFailed "do_goal_proj"

  and do_fst con : D.con compute =
    match con with
    | D.Abort -> ret D.Abort

    | D.Pair (con0, _) -> 
      ret con0

    | D.Cut {tp = D.Sg (base, _); cut; unfold} ->
      ret @@ cut_frm ~tp:base ~cut ~unfold D.KFst

    | _ -> 
      throw @@ NbeFailed "Couldn't fst argument in do_fst"

  and do_snd con : D.con compute =
    match con with
    | D.Abort -> ret D.Abort

    | D.Pair (_, con1) -> 
      ret con1

    | D.Cut {tp = D.Sg (_, fam); cut; unfold} ->
      let* fst = do_fst con in
      let+ fib = inst_tp_clo fam [fst] in 
      cut_frm ~tp:fib ~cut ~unfold D.KSnd

    | _ -> 
      throw @@ NbeFailed ("Couldn't snd argument in do_snd")


  and do_ap2 f a b = 
    let* fa = do_ap f a in
    do_ap fa b

  and do_ap f a =
    match f with
    | D.Abort -> ret D.Abort

    | D.Lam clo -> 
      inst_tm_clo clo [a]

    | D.Destruct dst ->
      do_destruct dst a

    | D.Cut {tp = D.Pi (base, fam); cut; unfold} ->
      let+ fib = inst_tp_clo fam [a] in
      cut_frm ~tp:fib ~cut ~unfold @@ D.KAp (base, a) 

    | _ -> 
      Format.eprintf "Bad: %a@." D.pp_con f;
      throw @@ NbeFailed "Not a function in do_ap"

  and do_destruct dst a =
    match dst, a with 
    | D.DCodePiSplit, D.CodePi (base, fam) 
    | D.DCodeSgSplit, D.CodeSg (base, fam) -> 
      ret @@ D.Pair (base, fam)
    | _ -> 
      throw @@ NbeFailed "Invalid destructor application"

  and do_sub_out v =
    match v with 
    | D.Abort -> ret D.Abort
    | D.SubIn con ->
      ret con
    | D.Cut {tp = D.Sub (tp, phi, clo); cut; unfold} ->
      ret @@ D.Cut {tp; cut = D.SubOut (cut, phi, clo), []; unfold = None} (* unfold ?? *)
    | _ ->
      throw @@ NbeFailed "do_sub_out"

  and do_el =
    function
    | D.Cut {cut; unfold = None} ->
      ret @@ D.El cut

    | D.Cut {unfold = Some lcon} ->
      do_el @<< force_lazy_con lcon

    | D.CodeNat ->
      ret D.Nat

    | D.CodePi (base, fam) ->
      quasiquote_tp @@ 
      QQ.foreign base @@ fun base ->
      QQ.foreign fam @@ fun fam ->
      QQ.term @@ 
      TB.pi (TB.el base) @@ fun x ->
      TB.el @@ TB.ap fam [x]

    | D.CodeSg (base, fam) ->
      quasiquote_tp @@ 
      QQ.foreign base @@ fun base ->
      QQ.foreign fam @@ fun fam ->
      QQ.term @@ 
      TB.sg (TB.el base) @@ fun x ->
      TB.el @@ TB.ap fam [x]

    | D.CodePath (fam, bdry) ->
      quasiquote_tp @@ 
      QQ.foreign fam @@ fun fam ->
      QQ.foreign bdry @@ fun bdry ->
      QQ.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.sub (TB.el (TB.ap fam [i])) (TB.boundary i) @@ fun prf ->
      TB.ap bdry [i]

    | _ ->
      CmpM.throw @@ NbeFailed "do_el failed"

  and do_coe r s (abs : D.con) con =
    test_sequent [] (Cof.eq r s) |>> function
    | true -> ret con 
    | _ -> do_rigid_coe abs r s con

  and do_rigid_coe (line : D.con) r s con =
    let i = D.DimProbe (Symbol.fresh ()) in
    let rec go peek =
      match peek with
      | D.CodePi _ ->
        let split_line = D.compose (D.Destruct D.DCodePiSplit) line in 
        quasiquote_tm @@
        QQ.foreign split_line @@ fun split_line ->
        QQ.foreign (D.dim_to_con r) @@ fun r ->
        QQ.foreign (D.dim_to_con s) @@ fun s ->
        QQ.foreign con @@ fun bdy ->
        let base_line = TB.fst split_line in
        let fam_line = TB.snd split_line in
        QQ.term @@ TB.Kan.coe_pi ~base_line ~fam_line ~r ~s ~bdy
      | D.CodeSg _ ->
        let split_line = D.compose (D.Destruct D.DCodeSgSplit) line in 
        quasiquote_tm @@
        QQ.foreign split_line @@ fun split_line ->
        QQ.foreign (D.dim_to_con r) @@ fun r ->
        QQ.foreign (D.dim_to_con s) @@ fun s ->
        QQ.foreign con @@ fun bdy ->
        let base_line = TB.fst split_line in
        let fam_line = TB.snd split_line in
        QQ.term @@ TB.Kan.coe_sg ~base_line ~fam_line ~r ~s ~bdy
      | D.CodePath _ ->
        raise Todo
      | D.Cut {unfold = Some lcon} -> 
        go @<< force_lazy_con lcon
      | D.Cut {cut; unfold = None} ->
        let hd = D.Coe (line, r, s, con) in
        let+ tp = do_el @<< do_ap line (D.dim_to_con s) in
        D.Cut {tp; cut = hd, []; unfold = None}
      | _ ->
        throw @@ NbeFailed "Invalid arguments to do_rigid_coe"
    in
    go @<< do_ap line (D.dim_to_con i)


  and do_rigid_hcom code r s phi (bdy : D.con) = 
    match code with 
    | D.CodePi (base, fam) ->
      quasiquote_tm @@
      QQ.foreign base @@ fun base ->
      QQ.foreign fam @@ fun fam ->
      QQ.foreign (D.dim_to_con r) @@ fun r ->
      QQ.foreign (D.dim_to_con s) @@ fun s ->
      QQ.foreign (D.cof_to_con phi) @@ fun phi ->
      QQ.foreign bdy @@ fun bdy ->
      QQ.term @@
      TB.Kan.hcom_pi ~base ~fam ~r ~s ~phi ~bdy
    | D.CodeSg (base, fam) ->
      quasiquote_tm @@
      QQ.foreign base @@ fun base ->
      QQ.foreign fam @@ fun fam ->
      QQ.foreign (D.dim_to_con r) @@ fun r ->
      QQ.foreign (D.dim_to_con s) @@ fun s ->
      QQ.foreign (D.cof_to_con phi) @@ fun phi ->
      QQ.foreign bdy @@ fun bdy ->
      QQ.term @@
      TB.Kan.hcom_sg ~base ~fam ~r ~s ~phi ~bdy
    | D.CodePath _ ->
      raise Todo
    | D.Cut {unfold = Some lcon} ->
      let* code = force_lazy_con lcon in 
      do_rigid_hcom code r s phi bdy
    | D.Cut {cut; unfold = None} ->
      let tp = D.El cut in
      let hd = D.HCom (cut, r, s, phi, bdy) in
      ret @@ D.Cut {tp; cut = hd, []; unfold = None}
    | _ ->
      throw @@ NbeFailed "Invalid arguments to do_rigid_hcom"

  and do_rigid_com (line : D.con) r s phi bdy =
    let* code_s = do_ap line (D.dim_to_con s) in
    do_rigid_hcom code_s r s phi @<<
    quasiquote_tm @@
    QQ.foreign (D.dim_to_con s) @@ fun s ->
    QQ.foreign line @@ fun line ->
    QQ.foreign bdy @@ fun bdy ->
    QQ.term @@ 
    TB.lam @@ fun i ->
    TB.lam @@ fun prf ->
    TB.coe line i s @@
    TB.ap bdy [i; prf]

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
    match Bwd.nth env.conenv i with 
    | v -> EvM.ret v 
    | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"
        
  let get_local_tp i =
    let* env = EvM.read_local in
    match Bwd.nth env.tpenv i with 
    | v -> EvM.ret v 
    | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

  let rec eval_tp (tp : S.tp) =
    match tp with
    | S.Nat -> ret D.Nat
    | S.Pi (base, fam) -> 
      let+ vbase = eval_tp base 
      and+ clfam = close_tp fam in
      D.Pi (vbase, clfam)
    | S.Sg (base, fam) -> 
      let+ vbase = eval_tp base 
      and+ clfam = close_tp fam in
      D.Sg (vbase, clfam)
    | S.Id (tp, left, right) ->
      let+ vtp = eval_tp tp
      and+ vl = eval left 
      and+ vr = eval right in
      D.Id (vtp, vl, vr)
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
      let cl = D.Clo (tm, env) in 
      D.Sub (tp, phi, cl)
    | S.TpDim  ->
      ret D.TpDim
    | S.TpCof -> 
      ret D.TpCof
    | S.TpPrf tphi ->
      let+ phi = eval_cof tphi in 
      D.TpPrf phi
    | S.TpVar ix ->
      get_local_tp ix

  and eval =
    function
    | S.Var i -> 
      let* con = get_local i in
      begin
        lift_cmp @@ whnf_con con |>> function
        | `Done -> ret con
        | `Reduce con -> ret con
      end
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
    | S.Coe (tpcode, tr, ts, tm) ->
      let* r = eval_dim tr in
      let* s = eval_dim ts in
      let* con = eval tm in
      begin
        CmpM.test_sequent [] (Cof.eq r s) |> lift_cmp |>> function
        | true -> 
          ret con
        | false -> 
          let* coe_abs = eval tpcode in
          lift_cmp @@ do_rigid_coe coe_abs r s con
      end
    | S.HCom (tpcode, tr, ts, tphi, tm) ->
      let* r = eval_dim tr in
      let* s = eval_dim ts in
      let* phi = eval_cof tphi in
      let* vtpcode = eval tpcode in
      begin
        CmpM.test_sequent [] (Cof.join (Cof.eq r s) phi) |> lift_cmp |>> function
        | true -> 
          append [D.dim_to_con s] @@ eval tm
        | false ->
          let* bdy = eval tm in 
          lift_cmp @@ do_rigid_hcom vtpcode r s phi bdy
      end
    | S.Com _ ->
      raise Todo
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
    | S.CofSplit (ttp, tphi0, tphi1, tm0, tm1) -> 
      let* tp = eval_tp ttp in
      let* phi0 = eval_cof tphi0 in
      let* phi1 = eval_cof tphi1 in 
      let* con = 
        let+ env = read_local in
        let pclo0 = D.Clo (tm0, env) in
        let pclo1 = D.Clo (tm1, env) in
        let hd = D.Split (tp, phi0, phi1, pclo0, pclo1) in
        D.Cut {tp; cut = hd, []; unfold = None} 
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


  and eval_dim tr =
    let* con = eval tr in
    lift_cmp @@ con_to_dim con

  and eval_cof tphi = 
    let* vphi = eval tphi in 
    lift_cmp @@ con_to_cof vphi

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
  val quote_cof : D.cof -> S.t quote
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

  let rec quote_con (tp : D.tp) con : S.t m =
    QuM.abort_if_inconsistent S.CofAbort @@ 
    match tp, con with 
    | _, D.Abort -> ret S.CofAbort
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
    | D.Id (tp, _, _), D.Refl con ->
      let+ t = quote_con tp con in 
      S.Refl t

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
          binder 1 @@
          let* var = top_var tpbase in
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
          binder 1 @@
          let* var = top_var tpbase in
          quote_con univ @<< 
          lift_cmp @@ do_ap fam var
        in
        S.Lam bdy
      in 
      S.CodeSg (tbase, tfam)
    | univ, D.CodePath (fam, bdry) -> (* check *)
      let* tfam = quote_con univ fam in
      let+ tbdry = quote_con univ bdry
      in
      S.CodePath(tfam, tbdry)
    | _ -> 
      Format.eprintf "bad: %a@." D.pp_con con;
      throw @@ NbeFailed "ill-typed quotation problem"

  and quote_tp (tp : D.tp) =
    match tp with
    | D.Nat -> ret S.Nat
    | D.Pi (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        binder 1 @@ 
        let* var = top_var base in
        quote_tp @<< 
        lift_cmp @@ inst_tp_clo fam [var]
      in
      S.Pi (tbase, tfam)
    | D.Sg (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        binder 1 @@ 
        let* var = top_var base in
        quote_tp @<< 
        lift_cmp @@ inst_tp_clo fam [var]
      in
      S.Sg (tbase, tfam)
    | D.Id (tp, left, right) ->
      let+ ttp = quote_tp tp 
      and+ tleft = quote_con tp left 
      and+ tright = quote_con tp right in 
      S.Id (ttp, tleft, tright)
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
          binder 1 @@ 
          let* i = top_dim_var in
          let* code = lift_cmp @@ do_ap abs @@ D.dim_to_con i in
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
      let* tpcode = quote_cut cut in
      let* tr = quote_dim r in
      let* ts = quote_dim s in
      let* tphi = quote_cof phi in
      let+ tbdy = 
        let+ tm = 
          binder 1 @@ 
          let* i = top_dim_var in
          begin
            bind_cof_proof (Cof.join (Cof.eq r i) phi) @@ 
            let* body = lift_cmp @@ do_ap2 bdy (D.dim_to_con i) D.Prf in 
            quote_con (D.El cut) body
          end |>> function
          | `Ret tm -> ret tm
          | `Abort -> ret S.CofAbort
        in 
        S.Lam (S.Lam tm)
      in
      S.HCom (tpcode, tr, ts, tphi, tbdy)
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
        let+ tr = quote_con D.TpDim @@ D.dim_to_con r 
        and+ ts = quote_con D.TpDim @@ D.dim_to_con s in
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
        let* x = top_var D.Nat in
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
        let* z = top_var @@ D.Id (tp, left, right) in 
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

  (* Invariant: tp0 and tp1 not necessarily whnf *)
  let rec equate_tp (tp0 : D.tp) (tp1 : D.tp) =
    QuM.abort_if_inconsistent () @@ 
    let* tp0 = contractum_or tp0 <@> lift_cmp @@ whnf_tp tp0 in
    let* tp1 = contractum_or tp1 <@> lift_cmp @@ whnf_tp tp1 in
    match tp0, tp1 with
    | D.TpDim, D.TpDim | D.TpCof, D.TpCof -> ret ()
    | D.TpPrf phi0, D.TpPrf phi1 -> 
      equate_cof phi0 phi1
    | D.Pi (base0, fam0), D.Pi (base1, fam1)
    | D.Sg (base0, fam0), D.Sg (base1, fam1) ->
      let* () = equate_tp base0 base1 in
      binder 1 @@ 
      let* x = top_var base0 in
      let* fib0 = lift_cmp @@ inst_tp_clo fam0 [x] in
      let* fib1 = lift_cmp @@ inst_tp_clo fam1 [x] in
      equate_tp fib0 fib1
    | D.Sub (tp0, phi0, clo0), D.Sub (tp1, phi1, clo1) ->
      let* () = equate_tp tp0 tp1 in
      let* () = equate_cof phi0 phi1 in
      under_cof phi0 @@ 
      binder 1 @@ 
      let* con0 = lift_cmp @@ inst_tm_clo clo0 [D.Prf] in
      let* con1 = lift_cmp @@ inst_tm_clo clo1 [D.Prf] in 
      equate_con tp0 con0 con1
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

  and under_cof phi m =
    let rec go cofs m =
      match cofs with 
      | [] -> m
      | (Cof.Var _ | Cof.Cof (Cof.Top | Cof.Bot | Cof.Eq _)) as phi :: cofs ->
        begin
          QuM.restrict phi @@ go cofs m |>> fun _ -> ret ()
        end
      | Cof.Cof (Cof.Meet (phi0, phi1)) :: cofs ->
        go (phi0 :: phi1 :: cofs) m
      | Cof.Cof (Cof.Join (phi0, phi1)) :: cofs ->
        let* () = go (phi0 :: cofs) m in 
        go (phi1 :: cofs) m
    in
    go [phi] m

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
    | _, _, D.Cut {cut = D.Split (_, phi0, phi1, _, _), []} ->
      under_cof (Cof.join phi0 phi1) @@ 
      equate_con tp con0 con1
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
    | D.Sub (tp, phi, _), _, _ ->
      under_cof phi @@
      let* out0 = lift_cmp @@ do_sub_out con0 in
      let* out1 = lift_cmp @@ do_sub_out con1 in
      equate_con tp out0 out1
    | D.Id (tp, _, _), D.Refl x, D.Refl y ->
      equate_con tp x y
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
      let* phi1 = lift_cmp @@ con_to_cof con0 in
      equate_cof phi0 phi1 
    | _, D.Cut {cut = cut0; unfold = None}, D.Cut {cut = cut1; unfold = None} ->
      equate_cut cut0 cut1

    | _, D.CodeNat, D.CodeNat ->
      ret ()

    | univ, D.CodePi (base0, fam0), D.CodePi (base1, fam1)
    | univ, D.CodeSg (base0, fam0), D.CodeSg (base1, fam1) ->
      let* _ = equate_con univ base0 base1 in
      let* el_base = lift_cmp @@ do_el base0 in
      let* fam_tp = 
        lift_cmp @@
        quasiquote_tp @@
        QQ.foreign base0 @@ fun base ->
        QQ.foreign_tp univ @@ fun univ ->
        QQ.term @@ TB.pi (TB.el base) @@ fun _ -> univ
      in
      equate_con fam_tp fam0 fam1

    | univ, D.CodePath (fam0, bdry0), D.CodePath (fam1, bdry1) ->
      let* famtp =
        lift_cmp @@
        quasiquote_tp @@
        QQ.foreign_tp univ @@ fun univ ->
        QQ.term @@ TB.pi TB.tp_dim @@ fun _ -> univ
      in
      let* _ = equate_con famtp fam0 fam1 in
      let* bdry_tp = 
        lift_cmp @@ quasiquote_tp @@ 
        QQ.foreign fam0 @@ fun fam ->
        QQ.term @@
        TB.pi TB.tp_dim @@ fun i ->
        let phi = TB.boundary i in
        TB.pi (TB.tp_prf phi) @@ fun prf ->
        TB.el @@ TB.ap fam [i]
      in
      equate_con bdry_tp bdry0 bdry1 

    | _ -> 
      throw @@ NbeFailed "unequal values"

  (* Invariant: cut0, cut1 are whnf *)
  and equate_cut cut0 cut1 = 
    let hd0, sp0 = cut0 in
    let hd1, sp1 = cut1 in
    match hd0, hd1 with
    | D.Split (_, phi0, phi1, _, _), _
    | _, D.Split (_, phi0, phi1, _, _) ->
      under_cof (Cof.join phi0 phi1) @@ 
      equate_cut cut0 cut1
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
        let* var = top_var D.Nat in
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
      let* x = top_var D.Nat in 
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
        let* p = top_var @@ D.Id (tp0, l, r) in
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
    | D.Coe (abs0, r0, s0, con0), D.Coe (abs1, r1, s1, con1) -> 
      let* () = equate_dim r0 r1 in
      let* () = equate_dim s0 s1 in
      let* () = 
        binder 1 @@ 
        let* i = top_dim_var in
        let* code0 = lift_cmp @@ do_ap abs0 @@ D.dim_to_con i in
        let* code1 = lift_cmp @@ do_ap abs1 @@ D.dim_to_con i in
        equate_con D.Univ code0 code1
      in
      let* code = lift_cmp @@ do_ap abs0 @@ D.dim_to_con r0 in
      let* tp = lift_cmp @@ do_el code in
      equate_con tp con0 con1
    | D.HCom (cut0, r0, s0, phi0, bdy0), D.HCom (cut1, r1, s1, phi1, bdy1) ->
      let* () = equate_cut cut0 cut1 in
      let* () = equate_dim r0 r1 in
      let* () = equate_dim s0 s1 in
      let* () = equate_cof phi0 phi1 in 
      binder 1 @@ 
      let* i = top_dim_var in
      under_cof (Cof.join (Cof.eq i r0) phi0) @@ binder 1 @@
      let* con0 = lift_cmp @@ do_ap2 bdy0 (D.dim_to_con i) D.Prf in
      let* con1 = lift_cmp @@ do_ap2 bdy1 (D.dim_to_con i) D.Prf in
      equate_con (D.El cut0) con0 con1
    | D.SubOut (cut0, _, _), D.SubOut (cut1, _, _) ->
      equate_cut cut0 cut1
    | _ ->
      throw @@ NbeFailed "Different heads"

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
    successful @@ equate_tp tp0 tp1

  let equal_cut cut0 cut1 = 
    successful @@ equate_cut cut0 cut1

  let equal_con tp con0 con1 = 
    successful @@ equate_con tp con0 con1
end

include Eval
include Quote
include Compute
