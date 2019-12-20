(* This file implements the normalization procedure. In addition the "unary" quotation
 * algorithm described by the paper, we also implement a binary operation for increased
 * efficiency. *)
module Syn = Syntax

module D = Domain

exception Nbe_failed of string

let rec do_rec tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec tp zero suc n)
  | D.Neutral {term = e; _} ->
    let final_tp = do_clos tp n in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero, suc, e)}
  | _ -> raise (Nbe_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp = D.Sg (t, _); term = ne} ->
    D.Neutral {tp = t; term = D.Fst ne}
  | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")

and do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sg (_, clo); term = ne} ->
    let fst = do_fst p in
    D.Neutral {tp = do_clos clo fst; term = D.Snd ne}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")

and do_clos clo a =
  match clo with
  | Clos {term; env} -> eval term (a :: env)
  | ConstClos t -> t

and do_clos2 (D.Clos2 {term; env}) a1 a2 = eval term (a2 :: a1 :: env)

and do_clos3 (D.Clos3 {term; env}) a1 a2 a3 = eval term (a3 :: a2 :: a1 :: env)

and do_j mot refl eq =
  match eq with
  | D.Refl t -> do_clos refl t
  | D.Neutral {tp; term} ->
    begin
      match tp with
      | D.Id (tp, left, right) ->
        D.Neutral
          { tp = do_clos3 mot left right eq;
            term = D.J (mot, refl, tp, left, right, term) }
      | _ -> raise (Nbe_failed "Not an Id in do_j")
    end
  | _ -> raise (Nbe_failed "Not a refl or neutral in do_j")

and do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos dst a in
        D.Neutral {tp = dst; term = D.Ap (e, D.Normal {tp = src; term = a})}
      | _ -> raise (Nbe_failed "Not a Pi in do_ap")
    end
  | _ -> raise (Nbe_failed "Not a function in do_ap")

and eval t (env : D.env) =
  match t with
  | Syn.Var i -> List.nth env i
  | Syn.Let (def, body) -> eval body (eval def env :: env)
  | Syn.Check (term, _) -> eval term env
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env)
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec
      (Clos {term = tp; env})
      (eval zero env)
      (Clos2 {term = suc; env})
      (eval n env)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (Clos {term = dest; env}))
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
  | Syn.Uni i -> D.Uni i
  | Syn.Sg (t1, t2) -> D.Sg (eval t1 env, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)
  | Syn.Refl t -> D.Refl (eval t env)
  | Syn.Id (tp, left, right) -> D.Id (eval tp env, eval left env, eval right env)
  | Syn.J (mot, refl, eq) ->
    do_j (D.Clos3 {term = mot; env}) (D.Clos {term = refl; env}) (eval eq env)

let rec read_back_nf size nf =
  match nf with
  (* Functions *)
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
    let arg = D.mk_var src size in
    let nf = D.Normal {tp = do_clos dest arg; term = do_ap f arg} in
    Syn.Lam (read_back_nf (size + 1) nf)
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst, snd); term = p} ->
    let fst' = do_fst p in
    let snd = do_clos snd fst' in
    let snd' = do_snd p in
    Syn.Pair
      (read_back_nf size (D.Normal { tp = fst; term = fst'}),
       read_back_nf size (D.Normal { tp = snd; term = snd'}))
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero} -> Syn.Zero
  | D.Normal {tp = D.Nat; term = D.Suc nf} ->
    Syn.Suc (read_back_nf size (D.Normal {tp = D.Nat; term = nf}))
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne; _}} -> read_back_ne size ne
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term} ->
    Syn.Refl (read_back_nf size (D.Normal {tp; term}))
  | D.Normal {tp = D.Id _; term = D.Neutral {term; _}} ->
    read_back_ne size term
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t} -> read_back_tp size t
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne; _}} -> read_back_ne size ne
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")

and read_back_tp size d =
  match d with
  | D.Neutral {term; _} -> read_back_ne size term
  | D.Nat -> Syn.Nat
  | D.Pi (src, dest) ->
    let var = D.mk_var src size in
    Syn.Pi (read_back_tp size src, read_back_tp (size + 1) (do_clos dest var))
  | D.Sg (fst, snd) ->
    let var = D.mk_var fst size in
    Syn.Sg (read_back_tp size fst, read_back_tp (size + 1) (do_clos snd var))
  | D.Id (tp, left, right) ->
    Syn.Id
      (read_back_tp size tp,
       read_back_nf size (D.Normal {tp; term = left}),
       read_back_nf size (D.Normal {tp; term = right}))
  | D.Uni k -> Syn.Uni k
  | _ -> raise (Nbe_failed "Not a type in read_back_tp")

and read_back_ne size ne =
  match ne with
  | D.Var x -> Syn.Var (size - (x + 1))
  | D.Ap (ne, arg) ->
    Syn.Ap (read_back_ne size ne, read_back_nf size arg)
  | D.NRec (tp, zero, suc, n) ->
    let tp_var = D.mk_var D.Nat size in
    let applied_tp = do_clos tp tp_var in
    let zero_tp = do_clos tp D.Zero in
    let applied_suc_tp = do_clos tp (D.Suc tp_var) in
    let tp' = read_back_tp (size + 1) applied_tp in
    let suc_var = D.mk_var applied_tp (size + 1) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' =
      read_back_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec
      (tp',
       read_back_nf size (D.Normal {tp = zero_tp; term = zero}),
       suc',
       read_back_ne size n)
  | D.Fst ne -> Syn.Fst (read_back_ne size ne)
  | D.Snd ne -> Syn.Snd (read_back_ne size ne)
  | D.J (mot, refl, tp, left, right, eq) ->
    let mot_var1 = D.mk_var tp size in
    let mot_var2 = D.mk_var tp (size + 1) in
    let mot_var3 = D.mk_var (D.Id (tp, left, right)) (size + 2) in
    let mot_syn = read_back_tp (size + 3) (do_clos3 mot mot_var1 mot_var2 mot_var3) in
    let refl_var = D.mk_var tp size in
    let refl_syn =
      read_back_nf
        (size + 1)
        (D.Normal {term = do_clos refl refl_var; tp = do_clos3 mot refl_var refl_var (D.Refl refl_var)}) in
    let eq_syn = read_back_ne size eq in
    Syn.J (mot_syn, refl_syn, eq_syn)

let rec check_nf size nf1 nf2 =
  match nf1, nf2 with
  (* Functions *)
  | D.Normal {tp = D.Pi (src1, dest1); term = f1},
    D.Normal {tp = D.Pi (_, dest2); term = f2} ->
    let arg = D.mk_var src1 size in
    let nf1 = D.Normal {tp = do_clos dest1 arg; term = do_ap f1 arg} in
    let nf2 = D.Normal {tp = do_clos dest2 arg; term = do_ap f2 arg} in
    check_nf (size + 1) nf1 nf2
  (* Pairs *)
  | D.Normal {tp = D.Sg (fst1, snd1); term = p1},
    D.Normal {tp = D.Sg (fst2, snd2); term = p2} ->
    let p11, p21 = do_fst p1, do_fst p2 in
    let snd1 = do_clos snd1 p11 in
    let snd2 = do_clos snd2 p21 in
    let p12, p22 = do_snd p1, do_snd p2 in
    check_nf size (D.Normal {tp = fst1; term = p11}) (D.Normal {tp = fst2; term = p21})
    && check_nf size (D.Normal {tp = snd1; term = p12}) (D.Normal {tp = snd2; term = p22})
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero},
    D.Normal {tp = D.Nat; term = D.Zero} -> true
  | D.Normal {tp = D.Nat; term = D.Suc nf1},
    D.Normal {tp = D.Nat; term = D.Suc nf2} ->
    check_nf size (D.Normal {tp = D.Nat; term = nf1}) (D.Normal {tp = D.Nat; term = nf2})
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Nat; term = D.Neutral {term = ne2; _}}-> check_ne size ne1 ne2
  (* Id *)
  | D.Normal {tp = D.Id (tp, _, _); term = D.Refl term1},
    D.Normal {tp = D.Id (_, _, _); term = D.Refl term2} ->
    check_nf size (D.Normal {tp; term = term1}) (D.Normal {tp; term = term2})
  | D.Normal {tp = D.Id _; term = D.Neutral {term = term1; _}},
    D.Normal {tp = D.Id _; term = D.Neutral {term = term2; _}} ->
    check_ne size term1 term2
  (* Types *)
  | D.Normal {tp = D.Uni _; term = t1}, D.Normal {tp = D.Uni _; term = t2} ->
    check_tp size t1 t2
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne1; _}},
    D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne2; _}} -> check_ne size ne1 ne2
  | _ -> false

and check_ne size ne1 ne2 =
  match ne1, ne2 with
  | D.Var x, D.Var y -> x = y
  | D.Ap (ne1, arg1), D.Ap (ne2, arg2) ->
    check_ne size ne1 ne2 && check_nf size arg1 arg2
  | D.NRec (tp1, zero1, suc1, n1), D.NRec (tp2, zero2, suc2, n2) ->
    let tp_var = D.mk_var D.Nat size in
    let applied_tp1, applied_tp2 = do_clos tp1 tp_var, do_clos tp2 tp_var in
    let zero_tp = do_clos tp1 D.Zero in
    let applied_suc_tp = do_clos tp1 (D.Suc tp_var) in
    let suc_var1 = D.mk_var applied_tp1 (size + 1) in
    let suc_var2 = D.mk_var applied_tp2 (size + 1) in
    let applied_suc1 = do_clos2 suc1 tp_var suc_var1 in
    let applied_suc2 = do_clos2 suc2 tp_var suc_var2 in
    check_tp (size + 1) applied_tp1 applied_tp2
    && check_nf size (D.Normal {tp = zero_tp; term = zero1}) (D.Normal {tp = zero_tp; term = zero2})
    && check_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc1})
      (D.Normal {tp = applied_suc_tp; term = applied_suc2})
    && check_ne size n1 n2
  | D.Fst ne1, D.Fst ne2  -> check_ne size ne1 ne2
  | D.Snd ne1, D.Snd ne2 -> check_ne size ne1 ne2
  | D.J (mot1, refl1, tp1, left1, right1, eq1),
    D.J (mot2, refl2, tp2, left2, right2, eq2) ->
    check_tp size tp1 tp2 &&
    check_nf size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp2; term = left2}) &&
    check_nf size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp2; term = right2}) &&
    let mot_var1 = D.mk_var tp1 size in
    let mot_var2 = D.mk_var tp1 (size + 1) in
    let mot_var3 = D.mk_var (D.Id (tp1, left1, right1)) (size + 2) in
    check_tp (size + 3) (do_clos3 mot1 mot_var1 mot_var2 mot_var3) (do_clos3 mot2 mot_var1 mot_var2 mot_var3) &&
    let refl_var = D.mk_var tp1 size in
    check_nf
      (size + 1)
      (D.Normal {term = do_clos refl1 refl_var; tp = do_clos3 mot1 refl_var refl_var (D.Refl refl_var)})
      (D.Normal {term = do_clos refl2 refl_var; tp = do_clos3 mot2 refl_var refl_var (D.Refl refl_var)}) &&
    check_ne size eq1 eq2
  | _ -> false

and check_tp size d1 d2 =
  match d1, d2 with
  | D.Neutral {term = term1; _}, D.Neutral {term = term2; _} ->
    check_ne size term1 term2
  | D.Nat, D.Nat -> true
  | D.Id (tp1, left1, right1), D.Id (tp2, left2, right2) ->
    check_tp size tp1 tp2 &&
    check_nf size (D.Normal {tp = tp1; term = left1}) (D.Normal {tp = tp1; term = left2}) &&
    check_nf size (D.Normal {tp = tp1; term = right1}) (D.Normal {tp = tp1; term = right2})
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let var = D.mk_var src' size in
    check_tp size src' src &&
    check_tp (size + 1) (do_clos dest var) (do_clos dest' var)
  | D.Sg (fst, snd), D.Sg (fst', snd') ->
    let var = D.mk_var fst size in
    check_tp size fst fst' &&
    check_tp (size + 1) (do_clos snd var) (do_clos snd' var)
  | D.Uni k, D.Uni j -> k = j 
  | _ -> false

let rec initial_env env =
  match env with
  | [] -> []
  | t :: env ->
    let env' = initial_env env in
    let d = D.Neutral {tp = eval t env'; term = D.Var (List.length env)} in
    d :: env'

let normalize ~env ~term ~tp =
  let env' = initial_env env in
  let tp = eval tp env' in
  let term = eval term env' in
  read_back_nf (List.length env') (D.Normal {tp; term})
