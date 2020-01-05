(* This file implements the normalization procedure. In addition the "unary" quotation
 * algorithm described by the paper, we also implement a binary operation for increased
 * efficiency. *)
module S = Syntax
module D = Domain

open NbeMonads

exception NbeFailed of string

module rec Compute : 
sig 
  val do_tp_clo : (S.tp, D.tp) D.clo -> D.t -> D.tp CmpM.m
  val do_tp_clo3 : S.tp D.clo3 -> D.t -> D.t -> D.t -> D.tp CmpM.m
  val do_tm_clo : (S.t, D.t) D.clo -> D.t -> D.t CmpM.m
  val do_tm_clo2 : S.t D.clo2 -> D.t -> D.t -> D.t CmpM.m
  val do_rec : (S.tp, D.tp) D.clo -> D.t -> S.t D.clo2 -> D.t -> D.t CmpM.m
  val do_fst : D.t -> D.t CmpM.m
  val do_snd : D.t -> D.t CmpM.m
  val do_ap : D.t -> D.t -> D.t CmpM.m
  val do_j : S.tp D.clo3 -> (S.t, D.t) D.clo -> D.t -> D.t CmpM.m
end =
struct
  open CmpM
  open Monad.Notation (CmpM)

  let rec do_rec (tp : (S.tp, D.tp) D.clo) zero suc n : D.t CmpM.m =
    match n with
    | D.Zero -> 
      ret zero
    | D.Suc n -> 
      let* v = do_rec tp zero suc n in 
      do_tm_clo2 suc n v
    | D.Ne {ne = e; _} ->
      let+ final_tp = do_tp_clo tp n in
      D.Ne {tp = final_tp; ne = D.NRec (tp, zero, suc, e)}
    | _ ->
      CmpM.throw @@ NbeFailed "Not a number"

  and do_fst p : D.t CmpM.m =
    match p with
    | D.Pair (p1, _) -> ret p1
    | D.Ne {tp = D.Sg (t, _); ne = ne} ->
      ret @@ D.Ne {tp = t; ne = D.Fst ne}
    | _ -> 
      throw @@ NbeFailed "Couldn't fst argument in do_fst"

  and do_snd p : D.t CmpM.m =
    match p with
    | D.Pair (_, p2) -> ret p2
    | D.Ne {tp = D.Sg (_, clo); ne = ne} ->
      let* fst = do_fst p in
      let+ fib = do_tp_clo clo fst in
      D.Ne {tp = fib; ne = D.Snd ne}
    | _ -> throw @@ NbeFailed "Couldn't snd argument in do_snd"

  and do_tp_clo clo a : D.tp CmpM.m =
    match clo with
    | Clo {term; env} -> 
      evaluate {D.locals = a :: env.locals} @@ 
      Eval.eval_tp term
    | ConstClo t -> 
      CmpM.ret t

  and do_tm_clo clo a =
    match clo with
    | D.Clo {term; env} -> 
      evaluate {D.locals = a :: env.locals} @@ 
      Eval.eval term
    | D.ConstClo t -> 
      CmpM.ret t

  and do_tm_clo2 (D.Clo2 {term; env}) a1 a2 = 
    evaluate {locals = a2 :: a1 :: env.locals} @@ 
    Eval.eval term

  and do_tp_clo2 (D.Clo2 {term; env}) a1 a2 = 
    evaluate {locals = a2 :: a1 :: env.locals} @@ 
    Eval.eval_tp term

  and do_tp_clo3 (D.Clo3 {term; env}) a1 a2 a3 =
    evaluate {locals = a3 :: a2 :: a1 :: env.locals} @@ 
    Eval.eval_tp term

  and do_j mot refl eq =
    match eq with
    | D.Refl t -> do_tm_clo refl t
    | D.Ne {tp; ne} -> 
      begin
        match tp with
        | D.Id (tp, left, right) ->
          let+ fib = do_tp_clo3 mot left right eq in
          D.Ne {tp = fib; ne = D.J (mot, refl, tp, left, right, ne)}
        | _ -> 
          CmpM.throw @@ NbeFailed "Not an Id in do_j"
      end
    | _ -> 
      CmpM.throw @@ NbeFailed "Not a refl or neutral in do_j"

  and do_ap f a =
    match f with
    | D.Lam clo -> 
      do_tm_clo clo a
    | D.Ne {tp; ne = e} ->
      begin
        match tp with
        | D.Pi (src, dst) ->
          let+ dst = do_tp_clo dst a in
          D.Ne {tp = dst; ne = D.Ap (e, D.Nf {tp = src; el = a})}
        | _ -> 
          CmpM.throw @@ NbeFailed "Not a Pi in do_ap"
      end
    | _ -> 
      CmpM.throw @@ NbeFailed "Not a function in do_ap"

end

and Eval :
sig
  val eval_tp : S.tp -> D.tp EvM.m
  val eval : S.t -> D.t EvM.m
end = 
struct 
  open EvM
  open Monad.Notation (EvM)

  let get_local i =
    let* env = EvM.read_local in
    match List.nth env.locals i with 
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

  and eval =
    function
    | S.Var i -> 
      get_local i 
    | S.Global sym -> 
      let+ st = EvM.read_global in
      let D.Nf nf = ElabState.get_global sym st in
      nf.el
    | S.Let (def, body) -> 
      let* vdef = eval def in 
      push [vdef] @@ eval body
    | S.Check (term, _) -> 
      eval term
    | S.Zero -> 
      ret D.Zero
    | S.Suc t -> 
      let+ el = eval t in 
      D.Suc el
    | S.NRec (tp, zero, suc, n) ->
      let* vzero = eval zero in
      let* vn = eval n in
      let* cltp = EvM.close_tp tp in
      let* clsuc = close2_tm suc in
      compute @@ Compute.do_rec cltp vzero clsuc vn
    | S.Lam t -> 
      let+ cl = close_tm t in
      D.Lam cl
    | S.Ap (t1, t2) -> 
      let* el1 = eval t1 in 
      let* el2 = eval t2 in
      compute @@ Compute.do_ap el1 el2
    | S.Pair (t1, t2) -> 
      let+ el1 = eval t1
      and+ el2 = eval t2 in
      D.Pair (el1, el2)
    | S.Fst t -> 
      let* el = eval t in 
      compute @@ Compute.do_fst el
    | S.Snd t -> 
      let* el = eval t in 
      compute @@ Compute.do_snd el
    | S.Refl t -> 
      let+ el = eval t in
      D.Refl el

    | S.J (mot, refl, eq) ->
      let* veq = eval eq in 
      let* clmot = close3_tp mot in
      let* clrefl = close_tm refl in
      compute @@ Compute.do_j clmot clrefl veq
end

module Quote : sig 
  val quote : D.tp -> D.t -> S.t QuM.m
  val quote_tp : D.tp -> S.tp QuM.m
  val quote_ne : D.ne -> S.t QuM.m
  val equal : D.tp -> D.t -> D.t -> bool QuM.m
  val equal_tp : D.tp -> D.tp -> bool QuM.m
  val equal_ne : D.ne -> D.ne -> bool QuM.m
end = 
struct
  open QuM
  open Monad.Notation (QuM)

  let top_var tp =
    let+ n = read_local in 
    D.mk_var tp @@ n - 1

  let rec quote tp el : S.t m =
    match tp, el with 
    | D.Pi (base, fam), f ->
      push 1 @@ 
      let* arg = top_var base in
      let* fib = compute @@ Compute.do_tp_clo fam arg in
      let* ap = compute @@ Compute.do_ap f arg in
      let+ body = quote fib ap in
      S.Lam body
    | D.Sg (base, fam), p ->
      let* fst = compute @@ Compute.do_fst p in
      let* snd = compute @@ Compute.do_snd p in
      let* fib = compute @@ Compute.do_tp_clo fam fst in 
      let+ tfst = quote base fst
      and+ tsnd = quote fib snd in 
      S.Pair (tfst, tsnd)
    | D.Nat, D.Zero ->
      ret S.Zero
    | D.Nat, D.Suc n ->
      let+ tn = quote D.Nat n in 
      S.Suc tn
    | D.Id (tp, _, _), D.Refl el ->
      let+ t = quote tp el in 
      S.Refl t
    | (D.Nat | D.Id _), D.Ne {ne; _} -> 
      quote_ne ne
    | _ -> 
      throw @@ NbeFailed "ill-typed quotation problem"

  and quote_tp =
    function
    | D.Nat -> ret S.Nat
    | D.Pi (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        push 1 @@ 
        let* var = top_var base in
        let* fib = compute @@ Compute.do_tp_clo fam var in
        quote_tp fib
      in
      S.Pi (tbase, tfam)
    | D.Sg (base, fam) ->
      let* tbase = quote_tp base in
      let+ tfam = 
        push 1 @@ 
        let* var = top_var base in
        let* fib = compute @@ Compute.do_tp_clo fam var in
        quote_tp fib
      in
      S.Sg (tbase, tfam)
    | D.Id (tp, left, right) ->
      let+ ttp = quote_tp tp 
      and+ tleft = quote tp left 
      and+ tright = quote tp right in 
      S.Id (ttp, tleft, tright)

  and quote_ne =
    function
    | D.Var x -> 
      let+ n = read_local in 
      S.Var (n - (x + 1))
    | D.Global sym ->
      ret @@ S.Global sym
    | D.NRec (mot, zero_case, suc_case, n) ->
      let* x, mot_x, tmot = 
        push 1 @@ 
        let* x = top_var D.Nat in
        let* mot_x = compute @@ Compute.do_tp_clo mot x in 
        let+ tmot = quote_tp mot_x in 
        x, mot_x, tmot
      in
      let+ tzero_case = 
        let* mot_zero = compute @@ Compute.do_tp_clo mot D.Zero in
        quote mot_zero zero_case
      and+ tsuc_case =
        push 2 @@
        let* ih = top_var mot_x in 
        let* mot_suc_x = compute @@ Compute.do_tp_clo mot @@ D.Suc x in 
        let* suc_case_x = compute @@ Compute.do_tm_clo2 suc_case x ih in
        quote mot_suc_x suc_case_x
      and+ tn = quote_ne n in
      S.NRec (tmot, tzero_case, tsuc_case, tn)
    | D.Fst ne ->
      let+ tne = quote_ne ne in
      S.Fst tne
    | D.Snd ne ->
      let+ tne = quote_ne ne in
      S.Snd tne
    | D.J (mot, refl_case, tp, left, right, eq) ->
      let* x, tmot =
        push 1 @@ 
        let* x = top_var tp in 
        push 1 @@ 
        let* y = top_var tp in 
        push 1 @@ 
        let* z = top_var @@ D.Id (tp, left, right) in 
        let* mot_xyz = compute @@ Compute.do_tp_clo3 mot x y z in 
        let+ tmot = quote_tp mot_xyz in 
        x, tmot
      in 
      let* trefl_case =
        push 1 @@ 
        let* mot_refl_x = compute @@ Compute.do_tp_clo3 mot x x (D.Refl x) in
        let* refl_case_x = compute @@ Compute.do_tm_clo refl_case x in
        quote mot_refl_x refl_case_x
      in
      let+ teq = quote_ne eq in
      S.J (tmot, trefl_case, teq)
    | D.Ap (ne, D.Nf nf) ->
      let+ tne = quote_ne ne
      and+ targ = quote nf.tp nf.el in
      S.Ap (tne, targ)


  let equal tp el1 el2 = 
    let+ t1 = quote tp el1
    and+ t2 = quote tp el2 in 
    t1 = t2

  let equal_tp tp1 tp2 = 
    let+ ttp1 = quote_tp tp1 
    and+ ttp2 = quote_tp tp2 in
    ttp1 = ttp2

  let equal_ne ne1 ne2 = 
    let+ tne1 = quote_ne ne1 
    and+ tne2 = quote_ne ne2 in
    tne1 = tne2
end

let eval_tp st env tp = 
  EvM.run (Eval.eval_tp tp) st env

let eval st env t = 
  EvM.run (Eval.eval t) st env

let do_tp_clo st clo el = 
  CmpM.run (Compute.do_tp_clo clo el) st

let do_tm_clo st clo el = 
  CmpM.run (Compute.do_tm_clo clo el) st

let quote_nf st size (D.Nf nf) =
  QuM.run (Quote.quote nf.tp nf.el) st size

let quote_tp st size tp =
  QuM.run (Quote.quote_tp tp) st size

let quote_ne st size ne = 
  QuM.run (Quote.quote_ne ne) st size


(* TODO: replace with efficient binary version *)
let equal_nf st size (D.Nf nf1) (D.Nf nf2) =
  QuM.run (Quote.equal nf1.tp nf1.el nf2.el) st size

let equal_ne st size ne1 ne2 =
  QuM.run (Quote.equal_ne ne1 ne2) st size

let equal_tp st size tp1 tp2 =
  QuM.run (Quote.equal_tp tp1 tp2) st size


module Monadic = 
struct
  include Eval
  include Quote
  include Compute
end