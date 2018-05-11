module Syn =
struct
  type uni_level = int
  type t =
    | Var of int (* DeBruijn indices for variables *)
    | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
    | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
    | Sig of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
    | Uni of uni_level

  type env = t list
end

module D =
struct
  type env = t list
  and clos = Clos of {term : Syn.t; env : env}
  and clos2 = Clos2 of {term : Syn.t; env : env}
  and t =
    | Lam of clos
    | Neutral of {tp : t; term : ne}
    | Nat
    | Zero
    | Suc of t
    | Pi of t * clos
    | Sig of t * clos
    | Pair of t * t
    | Uni of Syn.uni_level
  and ne =
    | Var of int (* DeBruijn levels for variables *)
    | Ap of ne * nf
    | Fst of ne
    | Snd of ne
    | NRec of clos * nf * clos2 * ne
  and nf =
    | Normal of {tp : t; term : t}
end

exception Nbe_failed of string

let mk_var tp lev = D.Neutral {tp; term = D.Var lev}

let rec do_rec env tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec env tp zero suc n)
  | D.Neutral {term = e} ->
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

and do_clos (Clos {term; env}) a = eval term (a :: env)

and do_clos2 (Clos2 {term; env}) a1 a2 = eval term (a2 :: a1 :: env)

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

and eval t env =
  match t with
  | Syn.Var i -> List.nth env i
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env)
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec
      env
      (Clos {term = tp; env})
      (eval zero env)
      (Clos2 {term = suc; env})
      (eval n env)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (Clos {term = dest; env}))
  | Syn.Uni i -> D.Uni i
  | Syn.Lam t -> D.Lam (Clos {term = t; env})
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
  | Syn.Sig (t1, t2) -> D.Sig (eval t1 env, (Clos {term = t2; env}))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)

let rec read_back_nf size nf =
  match nf with
  (* Functions *)
  | D.Normal {tp = D.Pi (src, dest); term = f} ->
    let arg = mk_var src size in
    let nf = D.Normal {tp = do_clos dest arg; term = do_ap f arg} in
    Syn.Lam (read_back_nf (size + 1) nf)
  (* Numbers *)
  | D.Normal {tp = D.Nat; term = D.Zero} -> Syn.Zero
  | D.Normal {tp = D.Nat; term = D.Suc nf} ->
    Syn.Suc (read_back_nf size (D.Normal {tp = D.Nat; term = nf}))
  | D.Normal {tp = D.Nat; term = D.Neutral {term = ne}} -> read_back_ne size ne
  (* Pairs *)
  | D.Normal {tp = D.Sig (fst, snd); term = p} ->
    let fst' = do_fst p in
    let snd = do_clos snd fst' in
    let snd' = do_snd p in
    Syn.Pair
      (read_back_nf size (D.Normal { tp = fst; term = fst'}),
       read_back_nf size (D.Normal { tp = snd; term = snd'}))
  (* Types *)
  | D.Normal {tp = D.Uni _; term = D.Nat} -> Syn.Nat
  | D.Normal {tp = D.Uni i; term = D.Pi (src, dest)} ->
    let var = mk_var src size in
    Syn.Pi
      (read_back_nf size (D.Normal {tp = D.Uni i; term = src}),
       read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos dest var}))
  | D.Normal {tp = D.Uni i; term = D.Sig (fst, snd)} ->
    let var = mk_var fst size in
    Syn.Sig
      (read_back_nf size (D.Normal {tp = D.Uni i; term = fst}),
       read_back_nf (size + 1) (D.Normal {tp = D.Uni i; term = do_clos snd var}))
  | D.Normal {tp = D.Uni _; term = D.Neutral {term = ne}} -> read_back_ne size ne
  | D.Normal {tp = D.Neutral _; term = D.Neutral {term = ne}} -> read_back_ne size ne
  | _ -> raise (Nbe_failed "Ill-typed read_back_nf")

and read_back_tp size d =
  match d with
  | D.Nat -> Syn.Nat
  | D.Pi (src, dest) ->
    let var = mk_var src size in
    Syn.Pi (read_back_tp size src, read_back_tp (size + 1) (do_clos dest var))
  | D.Sig (fst, snd) ->
    let var = mk_var fst size in
    Syn.Sig (read_back_tp size fst, read_back_tp (size + 1) (do_clos snd var))
  | D.Uni k -> Syn.Uni k
  | _ -> raise (Nbe_failed "Not a type in read_back_tp")

and read_back_ne size ne =
  match ne with
  | D.Var x -> Syn.Var (size - (x + 1))
  | D.Ap (ne, arg) ->
    Syn.Ap (read_back_ne size ne, read_back_nf size arg)
  | D.NRec (tp, zero, suc, n) ->
    let tp_var = mk_var D.Nat size in
    let applied_tp = do_clos tp tp_var in
    let applied_suc_tp = do_clos tp (D.Suc tp_var) in
    let tp' = read_back_tp (size + 1) applied_tp in
    let suc_var = mk_var applied_tp (size + 1) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' =
      read_back_nf (size + 2) (D.Normal {tp = applied_suc_tp; term = applied_suc}) in
    Syn.NRec (tp', read_back_nf size zero, suc', read_back_ne size n)
  | D.Fst ne -> Syn.Fst (read_back_ne size ne)
  | D.Snd ne -> Syn.Snd (read_back_ne size ne)

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
