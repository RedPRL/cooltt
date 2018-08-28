module Syn = Syntax

module D = Domain

exception Nbe_failed of string

let rec do_rec tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec tp zero suc n)
  | D.Neutral {term = e; _} ->
    let final_tp = do_clos tp n in
    let zero' = D.Normal {tp = do_clos tp D.Zero; term = zero} in
    D.Neutral {tp = final_tp; term = D.NRec (tp, zero', suc, e)}
  | _ -> raise (Nbe_failed "Not a number")

and do_fst p =
  match p with
  | D.Pair (p1, _) -> p1
  | D.Neutral {tp = D.Sig (t, _); term = ne} ->
    D.Neutral {tp = t; term = D.Fst ne}
  | _ -> raise (Nbe_failed "Couldn't fst argument in do_fst")

and do_snd p =
  match p with
  | D.Pair (_, p2) -> p2
  | D.Neutral {tp = D.Sig (_, clo); term = ne} ->
    let fst = do_fst p in
    D.Neutral {tp = do_clos clo fst; term = D.Snd ne}
  | _ -> raise (Nbe_failed "Couldn't snd argument in do_snd")

and do_clos clo a =
  match clo with
  | Clos {term; env} -> eval term (a :: env)
  | ConstClos t -> t

and do_tick_clos clo tick =
  match clo with
  | D.TickClos {term; env} -> eval term (tick :: env)
  | ConstTickClos t -> t

and do_clos2 (Clos2 {term; env}) a1 a2 = eval term (a2 :: a1 :: env)

and do_prev term tick =
  match term with
  | D.Next clos -> do_tick_clos clos tick
  | D.DFix (t, clos) ->
    begin
      match D.term_to_tick tick with
      | None -> do_clos clos (D.DFix (t, clos))
      | Some i -> D.Neutral {tp = t; term = D.Fix (t, clos, i)}
    end
  | D.Neutral {tp; term = e} ->
    begin
      match tp with
      | D.Later tp_clos ->
        let tp = do_tick_clos tp_clos tick in
        D.Neutral {tp; term = D.Prev (e, D.term_to_tick tick)}
      | _ -> raise (Nbe_failed "Not a later in do_prev")
    end
  | _ -> raise (Nbe_failed "Not a neutral, dfix, or next in do_prev")

and do_open t =
  match t with
  | D.Shut t -> t
  | D.Neutral {tp; term} ->
    begin
      match tp with
      | D.Box tp -> D.Neutral {tp; term = D.Open term}
      | _ -> raise (Nbe_failed "Not a box in do_open")
    end
  | _ -> raise (Nbe_failed "Not a box or neutral in open")

and do_unfold ~uni ~idx_tp ~tp ~idx ~fix ~tick =
  match tick with
  | D.Bullet -> fix
  | D.Tick i ->
    let tp_of_fix = D.Pi (idx_tp, ConstClos (D.Uni uni)) in
    D.Neutral
      { term = D.Unfold (uni, idx_tp, tp, idx, fix, i);
        tp =
          D.Neutral
            { tp = D.Uni uni;
              term =
                D.Ap (D.Fix (tp_of_fix, tp, i),
                      D.Normal {term = idx; tp = idx_tp})}}
  | _ -> raise (Nbe_failed "Not a tick in unfold")

and do_ap f a =
  match f with
  | D.Lam (_, clos) -> do_clos clos a
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
  | Syn.Lam (tp, t) -> D.Lam (eval tp env, Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
  | Syn.Uni i -> D.Uni i
  | Syn.Sig (t1, t2) -> D.Sig (eval t1 env, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)
  | Syn.Later t -> D.Later (TickClos {term = t; env = env})
  | Syn.Next t -> D.Next (TickClos {term = t; env = env})
  | Syn.Bullet -> D.Bullet
  | Syn.Prev (term, tick) -> do_prev (eval term env) (eval tick env)
  | Syn.DFix (tp, body) -> D.DFix (eval tp env, Clos {term = body; env = env})
  | Syn.Fold (_, _, _, _, t, Syn.Bullet) -> eval t env
  | Syn.Fold (uni, idx_tp, tp, idx, t, Syn.Var i) ->
    begin
      match List.nth env i with
      | D.Tick i ->
        D.Fold (uni, eval idx_tp env, D.Clos {term = tp; env}, eval idx env, eval t env, i)
      | D.Bullet -> eval t env
      | _ -> raise (Nbe_failed "Found a Fold with a tick")
    end
  | Syn.Fold _ -> raise (Nbe_failed "Found a Fold with a tick")
  | Syn.Unfold (uni, a, tp, idx, t, tick) ->
    do_unfold
      ~uni
      ~idx_tp:(eval a env)
      ~tp:(Clos {term = tp; env})
      ~idx:(eval idx env)
      ~fix:(eval t env)
      ~tick:(eval tick env)
  | Syn.Box t -> D.Box (eval t env)
  | Syn.Open t -> do_open (eval t env)
  | Syn.Shut t -> D.Shut (eval t env)

let rec read_back_nf size nf =
  match nf with
  (* Functions *)
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
    let arg = D.mk_var src size in
    let nf = D.Normal {tp = do_clos dest arg; term = do_ap f arg} in
    Syn.Lam (read_back_tp size src, read_back_nf (size + 1) nf)
  (* Pairs *)
  | D.Normal {tp = D.Sig (fst, snd); term = p} ->
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
  (* Later *)
  | D.Normal {term = D.Bullet; _} ->
    raise (Nbe_failed "Found bullet instead of a proper term in read_back_nf")
  | D.Normal {term = D.Tick _; _} ->
    raise (Nbe_failed "Found tick instead of a proper term in read_back_nf")
  | D.Normal {tp = D.Later tp; term} ->
    let nf = D.Normal {tp = do_tick_clos tp (D.Tick size); term = do_prev term (D.Tick size)} in
    Syn.Next (read_back_nf (size + 1) nf)
  | D.Normal {tp = _; term = D.Fold (uni, idx_tp, tp, idx, t, tick)} ->
    let tick = Syn.Var (size - (tick + 1)) in
    let fix_idx = D.Pi (idx_tp, D.ConstClos (D.Uni uni)) in
    let fix_tp = do_ap (do_clos tp (D.DFix (fix_idx, tp))) idx in
    let fix_syn = read_back_nf size (D.Normal {term = t; tp = fix_tp}) in
    let fix_var = D.mk_var (D.Later (D.ConstTickClos fix_idx)) size in
    Syn.Fold
      (uni,
       read_back_tp size idx_tp,
       read_back_nf (size + 1) (D.Normal {term = do_clos tp fix_var; tp = fix_idx}),
       read_back_nf size (D.Normal {term = idx; tp = idx_tp}),
       fix_syn,
       tick)
  (* Box *)
  | D.Normal {tp = D.Box tp; term} ->
    Syn.Shut (read_back_nf size (D.Normal {tp; term = do_open term}))
  (* Types *)
  | D.Normal {tp = D.Uni _; term = D.Nat} -> Syn.Nat
  | D.Normal {tp = D.Uni i; term = D.Box term} ->
    Syn.Box (read_back_nf size (D.Normal {tp = D.Uni i; term}))
  | D.Normal {tp = D.Uni i; term = D.Later t} ->
    let term = do_tick_clos t (Tick size) in
    Syn.Later (read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term}))
  | D.Normal {tp = D.Uni i; term = D.Pi (src, dest)} ->
    let var = D.mk_var src size in
    Syn.Pi
      (read_back_nf size (D.Normal {tp = D.Uni i; term = src}),
       read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos dest var}))
  | D.Normal {tp = D.Uni i; term = D.Sig (fst, snd)} ->
    let var = D.mk_var fst size in
    Syn.Sig
      (read_back_nf size (D.Normal {tp = D.Uni i; term = fst}),
       read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos snd var}))
  | D.Normal {tp = D.Uni _; term = D.Uni j} -> Syn.Uni j
  | D.Normal {tp = D.Uni _; term = D.Neutral {term = ne; _}} -> read_back_ne size ne
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne; _}} -> read_back_ne size ne
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")

and read_back_tp size d =
  match d with
  | D.Neutral {term; _} -> read_back_ne size term
  | D.Nat -> Syn.Nat
  | D.Pi (src, dest) ->
    let var = D.mk_var src size in
    Syn.Pi (read_back_tp size src, read_back_tp (size + 1) (do_clos dest var))
  | D.Sig (fst, snd) ->
    let var = D.mk_var fst size in
    Syn.Sig (read_back_tp size fst, read_back_tp (size + 1) (do_clos snd var))
  | D.Later t ->
    Syn.Later (read_back_tp (size + 1) (do_tick_clos t (D.Tick size)))
  | D.Box t -> Syn.Box (read_back_tp size t)
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
    let applied_suc_tp = do_clos tp (D.Suc tp_var) in
    let tp' = read_back_tp (size + 1) applied_tp in
    let suc_var = D.mk_var applied_tp (size + 1) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' =
      read_back_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec (tp', read_back_nf size zero, suc', read_back_ne size n)
  | D.Fst ne -> Syn.Fst (read_back_ne size ne)
  | D.Snd ne -> Syn.Snd (read_back_ne size ne)
  | D.Fix (tp, clos, i) ->
    let tick = Syn.Var (size - (i + 1)) in
    let sem_body = do_clos clos (D.mk_var (D.Later (D.ConstTickClos tp)) size) in
    let body = read_back_nf (size + 1) (D.Normal {tp; term = sem_body}) in
    Syn.Prev (Syn.DFix (read_back_tp size tp, body), tick)
  | D.Unfold (uni, idx_tp, tp, idx, fix, i) ->
    let tick = Syn.Var (size - (i + 1)) in
    let idx_nf = D.Normal {term = idx; tp = idx_tp} in
    let fix_idx = D.Pi (idx_tp, D.ConstClos (D.Uni uni)) in
    let fix_tp = D.Neutral {term = D.Ap (D.Fix (fix_idx, tp, i), idx_nf); tp = D.Uni uni} in
    let fix_syn = read_back_nf size (D.Normal {term = fix; tp = fix_tp}) in
    let fix_var = D.mk_var fix_idx size in
    Syn.Unfold
      (uni,
       read_back_tp size idx_tp,
       read_back_tp (size + 1) (do_clos tp fix_var),
       read_back_nf size idx_nf,
       fix_syn,
       tick)
  | D.Prev (ne, i) ->
    let tick = match i with
      | None -> Syn.Bullet
      | Some i -> Syn.Var (size - (i + 1)) in
    Syn.Prev (read_back_ne size ne, tick)
  | D.Open ne -> Syn.Open (read_back_ne size ne)

let rec check_subtype size d1 d2 =
  match d1, d2 with
  | D.Neutral {term = term1; _}, D.Neutral {term = term2; _} ->
    read_back_ne size term1 = read_back_ne size term2
  | D.Nat, D.Nat -> true
  | D.Pi (src, dest), D.Pi (src', dest') ->
    let var = D.mk_var src' size in
    check_subtype size src' src &&
    check_subtype (size + 1) (do_clos dest var) (do_clos dest' var)
  | D.Sig (fst, snd), D.Sig (fst', snd') ->
    let var = D.mk_var fst size in
    check_subtype size fst fst' &&
    check_subtype (size + 1) (do_clos snd var) (do_clos snd' var)
  | D.Later t, D.Later t' ->
    check_subtype (size + 1) (do_tick_clos t (D.Tick size)) (do_tick_clos t' (D.Tick size))
  | D.Box t, D.Box t' ->
    check_subtype size t t'
  | D.Uni k, D.Uni j -> k <= j
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
  let tp' = eval tp env' in
  let term' = eval term env' in
  read_back_nf (List.length env') (D.Normal {tp = tp'; term = term'})
