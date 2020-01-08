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
  val inst_tp_clo : 'n D.tp_clo -> ('n, D.con) Vec.vec -> D.tp CmpM.m
  val inst_tm_clo : 'n D.tm_clo -> ('n, D.con) Vec.vec -> D.con CmpM.m
  val do_nat_elim : ze su D.tp_clo -> D.con -> ze su su D.tm_clo -> D.con -> D.con CmpM.m
  val do_fst : D.con -> D.con CmpM.m
  val do_snd : D.con -> D.con CmpM.m
  val do_ap : D.con -> D.con -> D.con CmpM.m
  val do_id_elim : ze su su su D.tp_clo -> ze su D.tm_clo -> D.con -> D.con CmpM.m
  val do_frm : D.con -> D.frm -> D.con CmpM.m
  val do_spine : D.con -> D.frm list -> D.con CmpM.m

  val do_el : D.con -> D.tp CmpM.m
  val force_lazy_con : D.lazy_con ref -> D.con CmpM.m
end =
struct
  open CmpM
  open Monad.Notation (CmpM)

  let rec do_nat_elim (mot : ze su D.tp_clo) zero suc n : D.con CmpM.m =
    match n with
    | D.Zero -> 
      ret zero
    | D.Suc n -> 
      let* v = do_nat_elim mot zero suc n in 
      inst_tm_clo suc [n; v]
    | D.Cut {cut; _} ->
      let+ final_tp = inst_tp_clo mot [n] in
      let k = D.KNatElim (mot, zero, suc) in
      D.Cut {tp = final_tp; cut = push_frm k cut}
    | _ ->
      CmpM.throw @@ NbeFailed "Not a number"

  and do_fst p : D.con CmpM.m =
    match p with
    | D.Pair (p1, _) -> ret p1
    | D.Cut ({tp = D.Sg (base, _)} as gl) ->
      ret @@ D.Cut {tp = base; cut = push_frm D.KFst gl.cut} 
    | _ -> 
      throw @@ NbeFailed "Couldn't fst argument in do_fst"

  and push_frm k =
    function
    | cut, None -> 
      D.push k cut, None
    | cut, Some r -> 
      let s = ref @@
        match !r with
        | `Done con ->
          `Do (con, [k])
        | `Do (con, spine) ->
          `Do (con, spine @ [k])
      in 
      D.push k cut, Some s

  and do_snd p : D.con CmpM.m =
    match p with
    | D.Pair (_, p2) -> ret p2
    | D.Cut {tp = D.Sg (_, clo); cut} ->
      let* fst = do_fst p in
      let+ fib = inst_tp_clo clo [fst] in 
      D.Cut {tp = fib; cut = push_frm D.KSnd cut} 
    | _ -> throw @@ NbeFailed ("Couldn't snd argument in do_snd")

  and inst_tp_clo : type n. n D.tp_clo -> (n, D.con) Vec.vec -> D.tp CmpM.m =
    fun clo xs ->
    match clo with
    | Clo {bdy; env; _} -> 
      lift_ev {D.locals = env.locals <>< Vec.to_list xs} @@ 
      Eval.eval_tp bdy
    | ElClo clo ->
      let* con = inst_tm_clo clo xs in
      do_el con
    | ConstClo t -> 
      CmpM.ret t

  and inst_tm_clo : type n. n D.tm_clo -> (n, D.con) Vec.vec -> D.con CmpM.m =
    fun clo xs ->
    match clo with
    | D.Clo {bdy; env; spine} -> 
      let* con = 
        lift_ev {D.locals = env.locals <>< Vec.to_list xs} @@ 
        Eval.eval bdy
      in 
      do_spine con spine
    | D.ConstClo t -> 
      CmpM.ret t

  and do_id_elim mot refl eq =
    match eq with
    | D.Refl t -> inst_tm_clo refl [t]
    | D.Cut {tp; cut} -> 
      begin
        match tp with
        | D.Id (tp, left, right) ->
          let+ fib = inst_tp_clo mot [left; right; eq] in
          let k = D.KIdElim (mot, refl, tp, left, right) in
          D.Cut {tp = fib; cut = push_frm k cut}
        | _ -> 
          CmpM.throw @@ NbeFailed "Not an Id in do_id_elim"
      end
    | _ -> 
      CmpM.throw @@ NbeFailed "Not a refl or neutral in do_id_elim"

  and do_ap f a =
    match f with
    | D.Lam clo -> 
      inst_tm_clo clo [a]
    | D.Cut {tp; cut} ->
      begin
        match tp with
        | D.Pi (src, dst) ->
          let+ dst = inst_tp_clo dst [a] in
          let k = D.KAp (D.Nf {tp = src; con = a}) in
          D.Cut {tp = dst; cut = push_frm k cut}
        | _ -> 
          CmpM.throw @@ NbeFailed "Not a Pi in do_ap"
      end
    | _ -> 
      CmpM.throw @@ NbeFailed "Not a function in do_ap"

  and do_frm v =
    function
    | D.KAp (D.Nf nf) -> do_ap v nf.con
    | D.KFst -> do_fst v
    | D.KSnd -> do_snd v
    | D.KNatElim (mot, case_zero, case_suc) -> do_nat_elim mot case_zero case_suc v
    | D.KIdElim (mot, case_refl, _, _, _) -> do_id_elim mot case_refl v

  and do_spine v =
    function
    | [] -> ret v
    | k :: sp ->
      let* v' = do_frm v k in
      do_spine v' sp

  and do_el =
    function
    | D.Cut {cut = cut, None; tp = D.Univ} ->
      ret @@ D.El cut

    | D.Cut {cut = _, Some r; tp = D.Univ} ->
      let* con = force_lazy_con r in 
      do_el con

    | _ ->
      CmpM.throw @@ NbeFailed "do_el failed"

  and force_lazy_con r = 
    match !r with 
    | `Done con -> ret con
    | `Do (con, spine) -> 
      let+ con' = do_spine con spine in
      r := `Done con';
      con'
end

and Eval :
sig
  val eval_tp : S.tp -> D.tp EvM.m
  val eval : S.t -> D.con EvM.m
end = 
struct 
  open EvM
  open Monad.Notation (EvM)

  let get_local i =
    let* env = EvM.read_local in
    match Bwd.nth env.locals i with 
    | v -> EvM.ret v 
    | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

  let rec eval_tp t =
    match t with
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
      lift_cmp @@ Compute.do_el con

  and eval =
    function
    | S.Var i -> 
      get_local i 
    | S.Global sym -> 
      let* st = EvM.read_global in
      let D.Nf nf = ElabState.get_global sym st in
      let lcon = ref @@ `Done nf.con in
      ret @@ D.Cut {tp = nf.tp; cut = (D.Global sym, []), Some lcon}
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
    | S.NatElim (tp, zero, suc, n) ->
      let* vzero = eval zero in
      let* vn = eval n in
      let* cltp = EvM.close_tp tp in
      let* clsuc = close_tm suc in
      lift_cmp @@ Compute.do_nat_elim cltp vzero clsuc vn
    | S.Lam t -> 
      let+ cl = close_tm t in
      D.Lam cl
    | S.Ap (t1, t2) -> 
      let* el1 = eval t1 in 
      let* el2 = eval t2 in
      lift_cmp @@ Compute.do_ap el1 el2
    | S.Pair (t1, t2) -> 
      let+ el1 = eval t1
      and+ el2 = eval t2 in
      D.Pair (el1, el2)
    | S.Fst t -> 
      let* con = eval t in 
      lift_cmp @@ Compute.do_fst con
    | S.Snd t -> 
      let* con = eval t in 
      lift_cmp @@ Compute.do_snd con
    | S.Refl t -> 
      let+ con = eval t in
      D.Refl con
    | S.IdElim (mot, refl, eq) ->
      let* veq = eval eq in 
      let* clmot = close_tp mot in
      let* clrefl = close_tm refl in
      lift_cmp @@ Compute.do_id_elim clmot clrefl veq
end

module Quote : sig 
  val quote : D.tp -> D.con -> S.t QuM.m
  val quote_tp : D.tp -> S.tp QuM.m
  val quote_cut : D.cut -> S.t QuM.m
  val equal : D.tp -> D.con -> D.con -> bool QuM.m
  val equal_tp : D.tp -> D.tp -> bool QuM.m
  val equal_cut : D.cut -> D.cut -> bool QuM.m
end = 
struct
  open QuM
  open Monad.Notation (QuM)

  let top_var tp =
    let+ n = read_local in 
    D.mk_var tp @@ n - 1

  let rec quote tp con : S.t m =
    match tp, con with 
    | _, D.Cut {cut = (hd, sp), olcon; tp} ->
      begin
        match hd, olcon with
        | D.Global sym, Some lcon ->
          let* veil = read_veil in
          begin
            match Veil.policy sym veil with
            | `Transparent ->
              let* con = lift_cmp @@ Compute.force_lazy_con lcon in 
              quote tp con
            | _ ->
              quote_cut (hd, sp)
          end
        | _ -> 
          quote_cut (hd, sp)
      end
    | D.Pi (base, fam), f ->
      binder 1 @@ 
      let* arg = top_var base in
      let* fib = lift_cmp @@ Compute.inst_tp_clo fam [arg] in
      let* ap = lift_cmp @@ Compute.do_ap f arg in
      let+ body = quote fib ap in
      S.Lam body
    | D.Sg (base, fam), p ->
      let* fst = lift_cmp @@ Compute.do_fst p in
      let* snd = lift_cmp @@ Compute.do_snd p in
      let* fib = lift_cmp @@ Compute.inst_tp_clo fam [fst] in 
      let+ tfst = quote base fst
      and+ tsnd = quote fib snd in 
      S.Pair (tfst, tsnd)
    | D.Nat, D.Zero ->
      ret S.Zero
    | D.Nat, D.Suc n ->
      let+ tn = quote D.Nat n in 
      S.Suc tn
    | D.Id (tp, _, _), D.Refl con ->
      let+ t = quote tp con in 
      S.Refl t
    | _ -> 
      throw @@ NbeFailed "ill-typed quotation problem"

  and quote_tp =
    function
    | D.Nat -> ret S.Nat
    | D.Pi (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        binder 1 @@ 
        let* var = top_var base in
        let* fib = lift_cmp @@ Compute.inst_tp_clo fam [var] in
        quote_tp fib
      in
      S.Pi (tbase, tfam)
    | D.Sg (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        binder 1 @@ 
        let* var = top_var base in
        let* fib = lift_cmp @@ Compute.inst_tp_clo fam [var] in
        quote_tp fib
      in
      S.Sg (tbase, tfam)
    | D.Id (tp, left, right) ->
      let+ ttp = quote_tp tp 
      and+ tleft = quote tp left 
      and+ tright = quote tp right in 
      S.Id (ttp, tleft, tright)
    | D.Univ ->
      ret S.Univ
    | D.El cut ->
      let+ tm = quote_cut cut in
      S.El tm


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

  and quote_frm tm = 
    function
    | D.KNatElim (mot, zero_case, suc_case) ->
      let* x, mot_x, tmot = 
        binder 1 @@ 
        let* x = top_var D.Nat in
        let* mot_x = lift_cmp @@ Compute.inst_tp_clo mot [x] in 
        let+ tmot = quote_tp mot_x in 
        x, mot_x, tmot
      in
      let+ tzero_case = 
        let* mot_zero = lift_cmp @@ Compute.inst_tp_clo mot [D.Zero] in
        quote mot_zero zero_case
      and+ tsuc_case =
        binder 2 @@
        let* ih = top_var mot_x in 
        let* mot_suc_x = lift_cmp @@ Compute.inst_tp_clo mot [D.Suc x] in 
        let* suc_case_x = lift_cmp @@ Compute.inst_tm_clo suc_case [x; ih] in
        quote mot_suc_x suc_case_x
      in
      S.NatElim (tmot, tzero_case, tsuc_case, tm)
    | D.KIdElim (mot, refl_case, tp, left, right) ->
      let* x, tmot =
        binder 1 @@ 
        let* x = top_var tp in 
        binder 1 @@ 
        let* y = top_var tp in 
        binder 1 @@ 
        let* z = top_var @@ D.Id (tp, left, right) in 
        let* mot_xyz = lift_cmp @@ Compute.inst_tp_clo mot [x; y; z] in 
        let+ tmot = quote_tp mot_xyz in 
        x, tmot
      in 
      let+ trefl_case =
        binder 1 @@ 
        let* mot_refl_x = lift_cmp @@ Compute.inst_tp_clo mot [x; x; D.Refl x] in
        let* refl_case_x = lift_cmp @@ Compute.inst_tm_clo refl_case [x] in
        quote mot_refl_x refl_case_x
      in
      S.IdElim (tmot, trefl_case, tm)
    | D.KFst -> 
      ret @@ S.Fst tm
    | D.KSnd -> 
      ret @@ S.Snd tm
    | D.KAp (D.Nf nf) ->
      let+ targ = quote nf.tp nf.con in
      S.Ap (tm, targ)


  let equal tp el1 el2 = 
    let+ t1 = quote tp el1
    and+ t2 = quote tp el2 in 
    t1 = t2

  let rec equate_tp tp0 tp1 = 
    match tp0, tp1 with 
    | D.Pi (base0, fam0), D.Pi (base1, fam1) ->
      let* () = equate_tp base0 base1 in
      binder 1 @@ 
      let* x = top_var base0 in
      let* fib0 = lift_cmp @@ Compute.inst_tp_clo fam0 [x] in
      let* fib1 = lift_cmp @@ Compute.inst_tp_clo fam1 [x] in
      equate_tp fib0 fib1
    | D.Sg (base0, fam0), D.Sg (base1, fam1) ->
      let* () = equate_tp base0 base1 in
      binder 1 @@ 
      let* x = top_var base0 in
      let* fib0 = lift_cmp @@ Compute.inst_tp_clo fam0 [x] in
      let* fib1 = lift_cmp @@ Compute.inst_tp_clo fam1 [x] in
      equate_tp fib0 fib1
    | D.Id (tp0, l0, r0), D.Id (tp1, l1, r1) ->
      let* () = equate_tp tp0 tp1 in
      let* () = equate_con tp0 l0 l1 in
      equate_con tp0 r0 r1
    | D.Nat, D.Nat -> 
      ret ()
    | D.Univ, D.Univ ->
      ret ()
    | D.El cut0, D.El cut1 ->
      equate_cut cut0 cut1
    | _tp0, _tp1 -> 
      throw @@ NbeFailed ("Unequal types")

  and equate_con tp con0 con1 =
    match tp, con0, con1 with
    | D.Pi (base, fam), _, _ ->
      binder 1 @@ 
      let* x = top_var base in 
      let* fib = lift_cmp @@ Compute.inst_tp_clo fam [x] in 
      let* ap0 = lift_cmp @@ Compute.do_ap con0 x in
      let* ap1 = lift_cmp @@ Compute.do_ap con1 x in
      equate_con fib ap0 ap1
    | D.Sg (base, fam), _, _ ->
      let* fst0 = lift_cmp @@ Compute.do_fst con0 in
      let* fst1 = lift_cmp @@ Compute.do_fst con1 in
      let* () = equate_con base fst0 fst1 in
      let* fib = lift_cmp @@ Compute.inst_tp_clo fam [fst0] in
      let* snd0 = lift_cmp @@ Compute.do_snd con0 in
      let* snd1 = lift_cmp @@ Compute.do_snd con1 in
      equate_con fib snd0 snd1
    | _, D.Zero, D.Zero ->
      ret ()
    | _, D.Suc con0, D.Suc con1 ->
      equate_con tp con0 con1
    | _, D.Cut glued0, D.Cut glued1 ->
      begin 
        match glued0.cut, glued1.cut with 
        | (_, Some lcon0), (_, Some lcon1) ->
          let* con0' = lift_cmp @@ Compute.force_lazy_con lcon0 in 
          let* con1' = lift_cmp @@ Compute.force_lazy_con lcon1 in 
          equate_con tp con0' con1'
        | (cut0, None) , (cut1, None) ->
          equate_cut cut0 cut1
        | _ -> throw @@ NbeFailed "mismatch"
      end
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
    | D.KFst, D.KFst -> ret ()
    | D.KSnd, D.KSnd -> ret ()
    | D.KAp (D.Nf nf0), D.KAp (D.Nf nf1) ->
      let* () = equate_tp nf0.tp nf1.tp in
      equate_con nf0.tp nf0.con nf1.con 
    | D.KNatElim (mot0, zero_case0, suc_case0), D.KNatElim (mot1, zero_case1, suc_case1) ->
      let* fibx =
        binder 1 @@
        let* var = top_var D.Nat in
        let* fib0 = lift_cmp @@ Compute.inst_tp_clo mot0 [var] in
        let* fib1 = lift_cmp @@ Compute.inst_tp_clo mot1 [var] in
        let+ () = equate_tp fib0 fib1  in
        fib0 
      in
      let* () = 
        let* fib = lift_cmp @@ Compute.inst_tp_clo mot0 [D.Zero] in
        equate_con fib zero_case0 zero_case1
      in
      binder 1 @@
      let* x = top_var D.Nat in 
      binder 1 @@ 
      let* ih = top_var fibx in
      let* fib_sucx = lift_cmp @@ Compute.inst_tp_clo mot0 [D.Suc x] in
      let* con0 = lift_cmp @@ Compute.inst_tm_clo suc_case0 [x; ih] in
      let* con1 = lift_cmp @@ Compute.inst_tm_clo suc_case1 [x; ih] in
      equate_con fib_sucx con0 con1
    | D.KIdElim (mot0, refl_case0, tp0, left0, right0), D.KIdElim (mot1, refl_case1, tp1, left1, right1) ->
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
        let* fib0 = lift_cmp @@ Compute.inst_tp_clo mot0 [l; r; p] in
        let* fib1 = lift_cmp @@ Compute.inst_tp_clo mot1 [l; r; p] in
        equate_tp fib0 fib1
      in
      binder 1 @@
      let* x = top_var tp0 in
      let* fib_reflx = lift_cmp @@ Compute.inst_tp_clo mot0 [x; x; D.Refl x] in
      let* con0 = lift_cmp @@ Compute.inst_tm_clo refl_case0 [x] in
      let* con1 = lift_cmp @@ Compute.inst_tm_clo refl_case1 [x] in
      equate_con fib_reflx con0 con1
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
end

include Eval
include Quote
include Compute