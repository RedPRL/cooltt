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
  val whnf_con : D.con -> D.con compute
  val whnf_tp : D.tp -> D.tp compute

  val inst_tp_clo : 'n D.tp_clo -> ('n, D.con) Vec.vec -> D.tp compute
  val inst_tm_clo : 'n D.tm_clo -> ('n, D.con) Vec.vec -> D.con compute
  val inst_dim_con_clo : D.dim_clo -> D.dim -> D.con compute
  val do_nat_elim : ghost:D.ghost option -> ze su D.tp_clo -> D.con -> ze su su D.tm_clo -> D.con -> D.con compute
  val do_fst : D.con -> D.con compute
  val do_snd : D.con -> D.con compute
  val do_ap : D.con -> D.con -> D.con compute
  val do_id_elim : ghost:D.ghost option -> ze su su su D.tp_clo -> ze su D.tm_clo -> D.con -> D.con compute
  val do_goal_proj : D.con -> D.con compute
  val do_frm : D.con -> D.frm -> D.con compute
  val do_spine : D.con -> D.frm list -> D.con compute

  val do_el : D.con -> D.tp compute
  val force_lazy_con : D.lazy_con -> D.con compute
end =
struct
  open CmpM
  open Eval
  open Monad.Notation (CmpM)

  let rec whnf_con =
    function
    | D.Lam _ | D.Zero | D.Suc _ | D.Pair _ | D.Refl _ | D.GoalRet _ | D.TpCode _ | D.Cut {unfold = None} as con -> 
      ret con
    | D.Cut {unfold = Some lcon} -> 
      whnf_con @<< force_lazy_con lcon
    | D.PiCoe (abs, r, s, con) as picoe ->
      begin
        let* rs_eq = compare_dim r s in
        match rs_eq with
        | `Same -> whnf_con con
        | _ -> ret picoe
      end

  and whnf_tp = 
    function
    | tp -> ret tp

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

  and do_fst p : D.con compute =
    match p with
    | D.Pair (p1, _) -> ret p1
    | D.Cut {tp = D.Tp (D.Sg (base, _)); cut; unfold} ->
      ret @@ cut_frm ~tp:base ~cut ~unfold D.KFst
    | _ -> 
      throw @@ NbeFailed "Couldn't fst argument in do_fst"

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


  and push_frm k =
    function
    | cut, None -> 
      D.push k cut, None
    | cut, Some lcon -> 
      let s = 
        match lcon with
        | `Done con ->
          `Do (con, [k])
        | `Do (con, spine) ->
          `Do (con, spine @ [k])
      in 
      D.push k cut, Some s

  and do_snd p : D.con compute =
    match p with
    | D.Pair (_, p2) -> ret p2
    | D.Cut {tp = D.Tp (D.Sg (_, fam)); cut; unfold} ->
      let* fst = do_fst p in
      let+ fib = inst_tp_clo fam [fst] in 
      cut_frm ~tp:fib ~cut ~unfold D.KSnd
    | _ -> throw @@ NbeFailed ("Couldn't snd argument in do_snd")

  and inst_tp_clo : type n. n D.tp_clo -> (n, D.con) Vec.vec -> D.tp compute =
    fun clo xs ->
    match clo with
    | Clo {bdy; env; _} -> 
      let cons = Vec.to_list xs |> List.map @@ fun con -> `Con con in
      lift_ev (env <>< cons) @@ 
      eval_tp bdy
    | ElClo clo ->
      let* con = inst_tm_clo clo xs in
      do_el con

  and inst_tm_clo : type n. n D.tm_clo -> (n, D.con) Vec.vec -> D.con compute =
    fun clo xs ->
    match clo with
    | D.Clo {bdy; env} -> 
      let cons = Vec.to_list xs |> List.map @@ fun con -> `Con con in
      lift_ev (env <>< cons) @@ 
      eval bdy

  and inst_dim_con_clo : D.dim_clo -> D.dim -> D.con compute = 
    fun clo r ->
    match clo with 
    | D.DimClo (bdy, env) ->
      lift_ev (env <>< [`Dim r]) @@ eval bdy
    | D.PiCoeBaseClo clo -> 
      let* pi_code = inst_dim_con_clo clo.pi_clo r in
      let+ base, _ = dest_pi_code pi_code in
      base
    | D.PiCoeFibClo clo -> 
      let* pi_code = inst_dim_con_clo clo.pi_clo r in
      let* base, fam = dest_pi_code pi_code in
      let* arg_r = do_coe clo.dest r clo.base_abs clo.arg in
      inst_tm_clo fam [arg_r]

  and dest_pi_code con = 
    match con with 
    | D.TpCode (D.Pi (base, fam)) ->
      ret (base, fam)
    | _ ->
      CmpM.throw @@ NbeFailed "Expected pi code"

  and dest_pi_tp = 
    function
    | D.Tp (D.Pi (base, fam)) ->
      ret (base, fam)
    | _ ->
      CmpM.throw @@ NbeFailed "Expected pi type"

  and dest_id_tp =
    function
    | D.Tp (D.Id (tp, con0, con1)) ->
      ret (tp, con0, con1)
    | _ -> 
      CmpM.throw @@ NbeFailed "expected identity type"

  and do_goal_proj =
    function
    | D.GoalRet con -> ret con
    | D.Cut {tp = D.Tp (D.GoalTp (_, tp)); cut; unfold} ->
      ret @@ cut_frm ~tp ~cut ~unfold D.KGoalProj
    | _ ->
      CmpM.throw @@ NbeFailed "do_goal_proj"


  and do_ap f a =
    match f with
    | D.Lam clo -> 
      inst_tm_clo clo [a]

    | D.PiCoe (D.CoeAbs abs, r, s, f) ->
      let* peek_base, peek_fam = dest_pi_code abs.peek in
      let base_abs = D.CoeAbs {lvl = abs.lvl; peek = peek_base; clo = D.PiCoeBaseClo {pi_clo = abs.clo}} in
      let* fib_abs = 
        let* a_i = do_rigid_coe base_abs s (D.DimVar abs.lvl) a in
        let+ peek_fib = inst_tm_clo peek_fam [a_i] in
        D.CoeAbs {lvl = abs.lvl; peek = peek_fib; clo = D.PiCoeFibClo {dest = s; base_abs; arg = a; pi_clo = abs.clo}}
      in
      do_rigid_coe fib_abs r s @<< do_ap f @<< do_rigid_coe base_abs s r a

    | D.Cut {tp = D.Tp (D.Pi (base, fam)); cut; unfold} ->
      let+ fib = inst_tp_clo fam [a] in
      cut_frm ~tp:fib ~cut ~unfold @@ D.KAp (base, a) 

    | _ -> 
      CmpM.throw @@ NbeFailed "Not a function in do_ap"

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

  and force_lazy_con lcon : D.con m = 
    match lcon with 
    | `Done con -> ret con
    | `Do (con, spine) -> 
      do_spine con spine 

  and do_coe r s abs con =
    let* rs_eq = compare_dim r s in
    match rs_eq with
    | `Same -> ret con
    | _ -> do_rigid_coe abs r s con

  and do_rigid_coe (D.CoeAbs abs) r s con =
    match abs.peek with
    | D.TpCode (D.Pi _) ->
      ret @@ D.PiCoe (D.CoeAbs abs, r, s, con)
    | _ -> 
      failwith ""
end

and Eval :
sig
  val eval_tp : S.tp -> D.tp evaluate
  val eval : S.t -> D.con evaluate
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

  and eval =
    function
    | S.Var i -> 
      let* cell = get_local i in
      begin 
        match cell with
        | `Con con -> ret con
        | _ -> throw @@ NbeFailed "Expected `Con cell in environment"
      end
    | S.Global sym -> 
      let* st = EvM.read_global in
      let tp, con = ElabState.get_global sym st in
      ret @@ D.Cut {tp; cut = (D.Global sym, []); unfold = Some (`Done con)}
    | S.Let (def, body) -> 
      let* vdef = eval def in 
      append [`Con vdef] @@ eval body
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
    | S.Ap (t1, t2) -> 
      let* el1 = eval t1 in 
      let* el2 = eval t2 in
      lift_cmp @@ do_ap el1 el2
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

  and eval_ghost =
    function 
    | None -> 
      ret None
    | Some (lbl, cells) ->
      let rec go =
        function 
        | [] -> ret []
        | (tp, tm) :: cells -> 
          let* tp = eval_tp tp in 
          let* con = eval tm in
          let* cells = go cells in
          ret @@ (tp, con) :: cells
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
    | D.Pi (base, fam), f ->
      binder 1 @@ 
      let* arg = top_var base in
      let* fib = lift_cmp @@ inst_tp_clo fam [arg] in
      let* ap = lift_cmp @@ do_ap f arg in
      let+ body = quote_con fib ap in
      S.Lam body
    | D.Sg (base, fam), p ->
      let* fst = lift_cmp @@ do_fst p in
      let* snd = lift_cmp @@ do_snd p in
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


  and quote_hd =
    function
    | D.Var lvl -> 
      let+ n = read_local in 
      S.Var (n - (lvl + 1))
    | D.Global sym ->
      ret @@ S.Global sym

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
          let* ttp = quote_tp tp in
          let* tm = quote_con tp con in 
          let* cells = go cells in
          ret @@ (ttp, tm) :: cells
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


  let rec equate_tp tp0 tp1 = 
    let* D.Tp tp0 = lift_cmp @@ whnf_tp tp0 in
    let* D.Tp tp1 = lift_cmp @@ whnf_tp tp1 in
    match tp0, tp1 with 
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
    | D.El cut0, D.El cut1 ->
      equate_cut cut0 cut1
    | D.GoalTp (lbl0, tp0), D.GoalTp (lbl1, tp1) when lbl0 = lbl1 ->
      equate_tp tp0 tp1
    | _tp0, _tp1 -> 
      throw @@ NbeFailed ("Unequal types")

  and equate_con tp con0 con1 =
    let* D.Tp tp = lift_cmp @@ whnf_tp tp in 
    let* con0 = lift_cmp @@ whnf_con con0 in
    let* con1 = lift_cmp @@ whnf_con con1 in
    match tp, con0, con1 with
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
    | D.Id (tp, _, _), D.Refl x, D.Refl y ->
      equate_con tp x y
    | _, D.Zero, D.Zero ->
      ret ()
    | _, D.Suc con0, D.Suc con1 ->
      equate_con (D.Tp tp) con0 con1
    | _, D.Cut {cut = cut0; unfold = None}, D.Cut {cut = cut1; unfold = None} ->
      equate_cut cut0 cut1
    | _, (D.TpCode _ as con0), (D.TpCode _ as con1) -> 
      let* tp0 = lift_cmp @@ do_el con0 in
      let* tp1 = lift_cmp @@ do_el con1 in
      equate_tp tp0 tp1
    | _ -> 
      throw @@ NbeFailed ("Unequal values ")

  and equate_cut cut0 cut1 = 
    let hd0, sp0 = cut0 in
    let hd1, sp1 = cut1 in
    let* () = equate_hd hd0 hd1 in
    equate_spine sp0 sp1

  and equate_spine sp0 sp1 =
    match sp0, sp1 with
    | [], [] -> ret ()
    | k0 :: sp0, k1 :: sp1 ->
      let* () = equate_frm k0 k1 in 
      equate_spine sp0 sp1
    | _ -> 
      throw @@ NbeFailed "Spine length mismatch"

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
    | D.KGoalProj, D.KGoalProj ->
      ret ()
    | _ -> 
      throw @@ NbeFailed "Mismatched frames"

  and equate_hd hd0 hd1 = 
    match hd0, hd1 with
    | D.Global sym0, D.Global sym1 ->
      if Symbol.equal sym0 sym1 then ret () else 
        throw @@ NbeFailed "Different head symbols"
    | D.Var lvl0, D.Var lvl1 ->
      if lvl0 = lvl1 then ret () else
        throw @@ NbeFailed "Different head variables"
    | _ ->
      throw @@ NbeFailed "Different heads"


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