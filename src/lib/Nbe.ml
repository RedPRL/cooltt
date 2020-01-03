(* This file implements the normalization procedure. In addition the "unary" quotation
 * algorithm described by the paper, we also implement a binary operation for increased
 * efficiency. *)
module S = Syntax
module D = Domain

exception Nbe_failed of string

let rec do_rec st (tp : (S.tp, D.tp) D.clo) zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_tm_clo2 st suc n (do_rec st tp zero suc n)
  | D.Neutral {term = e; _} ->
    let final_tp = do_tp_clo st tp n in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero, suc, e)}
  | _ -> raise (Nbe_failed "Not a number")

and do_fst _st p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp = D.Sg (t, _); term = ne} ->
    D.Neutral {tp = t; term = D.Fst ne}
  | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")

and do_snd st p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sg (_, clo); term = ne} ->
    let fst = do_fst st p in
    D.Neutral {tp = do_tp_clo st clo fst; term = D.Snd ne}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")

and do_tp_clo st clo a =
  match clo with
  | Clo {term; env} -> eval_tp st {D.locals = a :: env.locals} term
  | ConstClo t -> t

and do_tm_clo st clo a =
  match clo with
  | D.Clo {term; env} -> eval st {D.locals = a :: env.locals} term
  | D.ConstClo t -> t

and do_tm_clo2 st (D.Clo2 {term; env}) a1 a2 = eval st {locals = a2 :: a1 :: env.locals} term

and do_tm_clo3 st (D.Clo3 {term; env}) a1 a2 a3 =
  eval st {locals = a3 :: a2 :: a1 :: env.locals} term

and do_tp_clo2 st (D.Clo2 {term; env}) a1 a2 = eval_tp st {locals = a2 :: a1 :: env.locals} term

and do_tp_clo3 st (D.Clo3 {term; env}) a1 a2 a3 =
  eval_tp st {locals = a3 :: a2 :: a1 :: env.locals} term

and do_j st mot refl eq =
  match eq with
  | D.Refl t -> do_tm_clo st refl t
  | D.Neutral {tp; term} -> 
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Neutral
          {tp = do_tp_clo3 st mot left right eq; 
           term = D.J (mot, refl, tp, left, right, term)}
      | _ -> raise (Nbe_failed "Not an Id in do_j")
    end
  | _ -> raise (Nbe_failed "Not a refl or neutral in do_j")

and do_ap st f a =
  match f with
  | D.Lam clo -> do_tm_clo st clo a
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_tp_clo st dst a in
        D.Neutral {tp = dst; term = D.Ap (e, D.Nf {tp = src; term = a})}
      | _ -> raise (Nbe_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Nbe_failed "Not a function in do_ap")

and eval_tp st env t =
  match t with
  | S.Nat -> D.Nat
  | S.Pi (src, dest) -> D.Pi (eval_tp st env src, Clo {term = dest; env})
  | S.Sg (t1, t2) -> D.Sg (eval_tp st env t1, Clo {term = t2; env})
  | S.Id (tp, left, right) ->
    D.Id (eval_tp st env tp, eval st env left, eval st env right)

and eval st (env : D.env) t =
  match t with
  | S.Var i -> List.nth env.locals i
  | S.Global sym -> 
    let D.Nf {term; _} = ElabState.get_global sym st in
    term
  | S.Let (def, body) -> eval st {locals = eval st env def :: env.locals} body
  | S.Check (term, _) -> eval st env term
  | S.Zero -> D.Zero
  | S.Suc t -> D.Suc (eval st env t)
  | S.NRec (tp, zero, suc, n) ->
    do_rec st
      (Clo {term = tp; env})
      (eval st env zero)
      (Clo2 {term = suc; env})
      (eval st env n)
  | S.Lam t -> D.Lam (Clo {term = t; env})
  | S.Ap (t1, t2) -> do_ap st (eval st env t1) (eval st env t2)
  | S.Pair (t1, t2) -> D.Pair (eval st env t1, eval st env t2)
  | S.Fst t -> do_fst st (eval st env t)
  | S.Snd t -> do_snd st (eval st env t)
  | S.Refl t -> D.Refl (eval st env t)
  | S.J (mot, refl, eq) ->
    do_j st
      (D.Clo3 {term = mot; env})
      (D.Clo {term = refl; env})
      (eval st env eq)

let rec read_back_nf st size nf =
  match nf with
  (* Functions *)
  | D.Nf {tp = D.Pi (src, dest); term = f} ->
    let arg = D.mk_var src size in
    let nf = D.Nf {tp = do_tp_clo st dest arg; term = do_ap st f arg} in
    S.Lam (read_back_nf st (size + 1) nf)
  (* Pairs *)
  | D.Nf {tp = D.Sg (fst, snd); term = p} ->
    let fst' = do_fst st p in
    let snd = do_tp_clo st snd fst' in
    let snd' = do_snd st p in
    S.Pair
      (read_back_nf st size (D.Nf {tp = fst; term = fst'}),
       read_back_nf st size (D.Nf {tp = snd; term = snd'}))
  (* Numbers *)
  | D.Nf {tp = D.Nat; term = D.Zero} -> S.Zero
  | D.Nf {tp = D.Nat; term = D.Suc nf} ->
    S.Suc (read_back_nf st size (D.Nf {tp = D.Nat; term = nf}))
  | D.Nf {tp = D.Nat; term = D.Neutral {term = ne; _}} ->
    read_back_ne st size ne
  (* Id *)
  | D.Nf {tp = D.Id (tp, _, _); term = D.Refl term} ->
    S.Refl (read_back_nf st size (D.Nf {tp; term}))
  | D.Nf {tp = D.Id _; term = D.Neutral {term; _}} -> read_back_ne st size term
  (* Types *)
  (* | D.Nf {tp = D.Neutral _; term = D.Neutral {term = ne; _}} ->
     read_back_Ne st size ne *)
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")

and read_back_tp st size d : S.tp =
  match d with
  | D.Nat -> S.Nat
  | D.Pi (src, dest) ->
    let var = D.mk_var src size in
    S.Pi (read_back_tp st size src, read_back_tp st (size + 1) (do_tp_clo st dest var))
  | D.Sg (fst, snd) ->
    let var = D.mk_var fst size in
    S.Sg (read_back_tp st size fst, read_back_tp st (size + 1) (do_tp_clo st snd var))
  | D.Id (tp, left, right) ->
    S.Id
      (read_back_tp st size tp,
       read_back_nf st size (D.Nf {tp; term = left}),
       read_back_nf st size (D.Nf {tp; term = right}))

and read_back_ne st size ne =
  match ne with
  | D.Var x -> S.Var (size - (x + 1))
  | D.Global sym -> S.Global sym
  | D.Ap (ne, arg) -> S.Ap (read_back_ne st size ne, read_back_nf st size arg)
  | D.NRec (tp, zero, suc, n) ->
    let tp_var = D.mk_var D.Nat size in
    let applied_tp = do_tp_clo st tp tp_var in
    let zero_tp = do_tp_clo st tp D.Zero in
    let applied_suc_tp = do_tp_clo st tp (D.Suc tp_var) in
    let tp' = read_back_tp st (size + 1) applied_tp in
    let suc_var = D.mk_var applied_tp (size + 1) in
    let applied_suc = do_tm_clo2 st suc tp_var suc_var in
    let suc' =
      read_back_nf st (size + 2)
        (D.Nf {tp = applied_suc_tp; term = applied_suc})
    in
    S.NRec
      (tp',
       read_back_nf st size (D.Nf {tp = zero_tp; term = zero}),
       suc',
       read_back_ne st size n)
  | D.Fst ne -> S.Fst (read_back_ne st size ne)
  | D.Snd ne -> S.Snd (read_back_ne st size ne)
  | D.J (mot, refl, tp, left, right, eq) ->
    let mot_var1 = D.mk_var tp size in
    let mot_var2 = D.mk_var tp (size + 1) in
    let mot_var3 = D.mk_var (D.Id (tp, left, right)) (size + 2) in
    let mot_syn = read_back_tp st (size + 3) (do_tp_clo3 st mot mot_var1 mot_var2 mot_var3) in
    let refl_var = D.mk_var tp size in
    let refl_syn = read_back_nf st (size + 1) (D.Nf {term = do_tm_clo st refl refl_var; tp = do_tp_clo3 st mot refl_var refl_var (D.Refl refl_var)})
    in
    let eq_syn = read_back_ne st size eq in
    S.J (mot_syn, refl_syn, eq_syn)

let rec equal_nf st size nf1 nf2 =
  match nf1, nf2 with
  (* Functions *)
  | ( D.Nf {tp = D.Pi (src1, dest1); term = f1},
      D.Nf {tp = D.Pi (_, dest2); term = f2} ) ->
    let arg = D.mk_var src1 size in
    let nf1 = D.Nf {tp = do_tp_clo st dest1 arg; term = do_ap st f1 arg} in
    let nf2 = D.Nf {tp = do_tp_clo st dest2 arg; term = do_ap st f2 arg} in
    equal_nf st (size + 1) nf1 nf2
  (* Pairs *)
  | ( D.Nf {tp = D.Sg (fst1, snd1); term = p1},
      D.Nf {tp = D.Sg (fst2, snd2); term = p2} ) ->
    let p11, p21 = do_fst st p1, do_fst st p2 in
    let snd1 = do_tp_clo st snd1 p11 in
    let snd2 = do_tp_clo st snd2 p21 in
    let p12, p22 = do_snd st p1, do_snd st p2 in
    equal_nf st size
      (D.Nf {tp = fst1; term = p11})
      (D.Nf {tp = fst2; term = p21})
    && equal_nf st size
      (D.Nf {tp = snd1; term = p12})
      (D.Nf {tp = snd2; term = p22})
  (* Numbers *)
  | D.Nf {tp = D.Nat; term = D.Zero}, D.Nf {tp = D.Nat; term = D.Zero} ->
    true
  | D.Nf {tp = D.Nat; term = D.Suc nf1}, D.Nf {tp = D.Nat; term = D.Suc nf2}
    ->
    equal_nf st size
      (D.Nf {tp = D.Nat; term = nf1})
      (D.Nf {tp = D.Nat; term = nf2})
  | ( D.Nf {tp = D.Nat; term = D.Neutral {term = ne1; _}},
      D.Nf {tp = D.Nat; term = D.Neutral {term = ne2; _}} ) ->
    equal_ne st size ne1 ne2
  (* Id *)
  | ( D.Nf {tp = D.Id (tp, _, _); term = D.Refl term1},
      D.Nf {tp = D.Id (_, _, _); term = D.Refl term2} ) ->
    equal_nf st size (D.Nf {tp; term = term1}) (D.Nf {tp; term = term2})
  | ( D.Nf {tp = D.Id _; term = D.Neutral {term = term1; _}},
      D.Nf {tp = D.Id _; term = D.Neutral {term = term2; _}} ) ->
    equal_ne st size term1 term2
  | _ -> false

and equal_ne st size ne1 ne2 =
  match ne1, ne2 with
  | D.Var x, D.Var y -> x = y
  | D.Global sym, D.Global sym' -> Symbol.equal sym sym'
  | D.Ap (ne1, arg1), D.Ap (ne2, arg2) ->
    equal_ne st size ne1 ne2 && equal_nf st size arg1 arg2
  | D.NRec (tp1, zero1, suc1, n1), D.NRec (tp2, zero2, suc2, n2) ->
    let tp_var = D.mk_var D.Nat size in
    let applied_tp1, applied_tp2 =
      do_tp_clo st tp1 tp_var, do_tp_clo st tp2 tp_var
    in
    let zero_tp = do_tp_clo st tp1 D.Zero in
    let applied_suc_tp = do_tp_clo st tp1 (D.Suc tp_var) in
    let suc_var1 = D.mk_var applied_tp1 (size + 1) in
    let suc_var2 = D.mk_var applied_tp2 (size + 1) in
    let applied_suc1 = do_tm_clo2 st suc1 tp_var suc_var1 in
    let applied_suc2 = do_tm_clo2 st suc2 tp_var suc_var2 in
    equal_tp st (size + 1) applied_tp1 applied_tp2
    && equal_nf st size
      (D.Nf {tp = zero_tp; term = zero1})
      (D.Nf {tp = zero_tp; term = zero2})
    && equal_nf st (size + 2)
      (D.Nf {tp = applied_suc_tp; term = applied_suc1})
      (D.Nf {tp = applied_suc_tp; term = applied_suc2})
    && equal_ne st size n1 n2
  | D.Fst ne1, D.Fst ne2 -> equal_ne st size ne1 ne2
  | D.Snd ne1, D.Snd ne2 -> equal_ne st size ne1 ne2
  | ( D.J (mot1, refl1, tp1, left1, right1, eq1),
      D.J (mot2, refl2, tp2, left2, right2, eq2) ) ->
    equal_tp st size tp1 tp2
    && equal_nf st size
      (D.Nf {tp = tp1; term = left1})
      (D.Nf {tp = tp2; term = left2})
    && equal_nf st size
      (D.Nf {tp = tp1; term = right1})
      (D.Nf {tp = tp2; term = right2})
    &&
    let mot_var1 = D.mk_var tp1 size in
    let mot_var2 = D.mk_var tp1 (size + 1) in
    let mot_var3 = D.mk_var (D.Id (tp1, left1, right1)) (size + 2) in
    equal_tp st (size + 3)
      (do_tp_clo3 st mot1 mot_var1 mot_var2 mot_var3)
      (do_tp_clo3 st mot2 mot_var1 mot_var2 mot_var3)
    &&
    let refl_var = D.mk_var tp1 size in
    equal_nf st (size + 1)
      (D.Nf
         {
           term = do_tm_clo st refl1 refl_var;
           tp = do_tp_clo3 st mot1 refl_var refl_var (D.Refl refl_var);
         })
      (D.Nf
         {
           term = do_tm_clo st refl2 refl_var;
           tp = do_tp_clo3 st mot2 refl_var refl_var (D.Refl refl_var);
         })
    && equal_ne st size eq1 eq2
  | _ -> false

and equal_tp st size d1 d2 =
  match d1, d2 with
  | D.Nat, D.Nat -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    equal_tp st size tp1 tp2
    && equal_nf st size
      (D.Nf {tp = tp1; term = left1})
      (D.Nf {tp = tp1; term = left2})
    && equal_nf st size
      (D.Nf {tp = tp1; term = right1})
      (D.Nf {tp = tp1; term = right2})
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let var = D.mk_var src' size in
    equal_tp st size src' src
    && equal_tp st (size + 1) (do_tp_clo st dest var) (do_tp_clo st dest' var)
  | D.Sg (fst, snd), D.Sg (fst', snd') ->
    let var = D.mk_var fst size in
    equal_tp st size fst fst'
    && equal_tp st (size + 1) (do_tp_clo st snd var) (do_tp_clo st snd' var)
  | _ -> false