module Syn =
struct
  type uni_level = int
  type t =
    | Var of int (* DeBruijn indices for variables *)
    | Nat | Zero | Suc of t | NRec of t * t * t * t
    | Pi of t * t | Lam of t | Ap of t * t
    | Sig of t * t | Pair of t * t | Fst of t | Snd of t
    | Uni of uni_level
    | Subst of t * subst
  and subst =
    | Shift
    | Id
    | Compose of subst * subst
    | First of subst * t

  type env = t list
end

module D =
struct
  type env = t list
  and clos = Syn.t * env
  and clos2 = Syn.t * env
  and ann_clos = Syn.t * t * env
  and t =
    | Lam of clos
    | Neutral of t * ne
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
    | NRec of ann_clos * nf * clos2 * ne
  and nf =
    | Normal of t * t
end

let mk_var tp lev = D.Neutral (tp, D.Var lev)

let rec apply_subst sub env =
  match sub with
  | Syn.Shift -> List.tl env
  | Syn.Id -> env
  | Syn.Compose (sub1, sub2) -> apply_subst sub2 env |> apply_subst sub1
  | Syn.First (sub, t) -> eval t env :: apply_subst sub env

and do_rec env tp zero suc n =
  match n with
  | D.Zero -> zero
  | D.Suc n -> do_clos2 suc n (do_rec env tp zero suc n)
  | D.Neutral (_, e) ->
    let final_tp = do_ann_clos tp n in
    let zero' = D.Normal (do_ann_clos tp D.Zero, zero) in
    D.Neutral (final_tp, D.NRec (tp, zero', suc, e))
  | _ -> failwith "Not a number"

and do_fst p =
  match p with
  | D.Pair (p1, p2) -> p1
  | D.Neutral (D.Sig (t, clo), ne) ->
    D.Neutral(t, D.Fst ne)
  | _ -> failwith "Couldn't fst argument in do_fst"

and do_snd p =
  match p with
  | D.Pair (p1, p2) -> p2
  | D.Neutral (D.Sig (t, clo), ne) ->
    let fst = do_fst p in
    D.Neutral (do_clos clo fst, D.Snd ne)
  | _ -> failwith "Couldn't snd argument in do_snd"

and do_clos (t, env) a = eval t (a :: env)

and do_clos2 (t, env) a1 a2 = eval t (a2 :: a1 :: env)

and do_ann_clos (t, _, env) a = eval t (a :: env)

and do_ap f a =
  match f with
  | D.Lam clos -> do_clos clos a
  | D.Neutral (tp, e) ->
    begin
      match tp with
      | D.Pi (src, dst) ->
        let dst = do_clos dst a in
        D.Neutral (dst, D.Ap (e, D.Normal (src, a)))
      | _ -> failwith "Not a Pi in do_ap"
    end
  | _ -> failwith "Not a function in do_ap"

and eval t env =
  match t with
  | Syn.Var i -> List.nth env i
  | Syn.Nat -> D.Nat
  | Syn.Zero -> D.Zero
  | Syn.Suc t -> D.Suc (eval t env)
  | Syn.NRec (tp, zero, suc, n) ->
    do_rec env (tp, D.Nat, env) (eval zero env) (suc, env) (eval n env)
  | Syn.Pi (src, dest) ->
    D.Pi (eval src env, (dest, env))
  | Syn.Uni i -> D.Uni i
  | Syn.Lam t -> D.Lam (t, env)
  | Syn.Ap (t1, t2) -> do_ap (eval t1 env) (eval t2 env)
  | Syn.Subst (t, subst) -> eval t (apply_subst subst env)
  | Syn.Sig (t1, t2) -> D.Sig (eval t1 env, (t2, env))
  | Syn.Pair (t1, t2) -> D.Pair (eval t1 env, eval t2 env)
  | Syn.Fst t -> do_fst (eval t env)
  | Syn.Snd t -> do_snd (eval t env)

let rec read_back_nf size nf =
  match nf with
  (* Functions *)
  | D.Normal (D.Pi (src, dest), f) ->
    let arg = mk_var src size in
    let nf = D.Normal (do_clos dest arg, do_ap f arg) in
    Syn.Lam (read_back_nf (size + 1) nf)
  (* Numbers *)
  | D.Normal (D.Nat, D.Zero) -> Syn.Zero
  | D.Normal (D.Nat, D.Suc nf) -> Syn.Suc (read_back_nf size (D.Normal (D.Nat, nf)))
  | D.Normal (D.Nat, D.Neutral (_, ne)) -> read_back_ne size ne
  (* Pairs *)
  | D.Normal (D.Sig (fst, snd), p) ->
    let fst' = do_fst p in
    let snd = do_clos snd fst' in
    let snd' = do_snd p in
    Syn.Pair
      (read_back_nf size (D.Normal (fst, fst')),
       read_back_nf size (D.Normal (snd, snd')))
  (* Types *)
  | D.Normal (D.Uni _, D.Nat) -> Syn.Nat
  | D.Normal (D.Uni i, D.Pi (src, dest)) ->
    let var = mk_var src size in
    Syn.Pi
      (read_back_nf size (D.Normal (D.Uni i, src)),
       read_back_nf (size + 1) (D.Normal (D.Uni i, do_clos dest var)))
  | D.Normal (D.Uni i, D.Sig (fst, snd)) ->
    let var = mk_var fst size in
    Syn.Sig
      (read_back_nf size (D.Normal (D.Uni i, fst)),
       read_back_nf (size + 1) (D.Normal (D.Uni i, do_clos snd var)))
  | D.Normal (D.Uni _, D.Neutral (_, ne)) -> read_back_ne size ne
  | D.Normal (D.Neutral (_, _), D.Neutral (_, ne)) -> read_back_ne size ne
  | _ -> failwith "Ill-typed read_back_nf"

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
  | _ -> failwith "Not a type in read_back_tp"

and read_back_ne size ne =
  match ne with
  | D.Var x -> Syn.Var (size - (x + 1))
  | D.Ap (ne, arg) ->
    Syn.Ap (read_back_ne size ne, read_back_nf size arg)
  | D.NRec ((_, tp_tp, _) as tp, zero, suc, n) ->
    let tp_var = mk_var tp_tp size in
    let applied_tp = do_ann_clos tp tp_var in
    let applied_suc_tp = do_ann_clos tp (D.Suc tp_var) in
    let tp' = read_back_tp (size + 1) applied_tp in
    let suc_var = mk_var applied_tp (size + 1) in
    let applied_suc = do_clos2 suc tp_var suc_var in
    let suc' = read_back_nf (size + 2) (D.Normal (applied_suc_tp, applied_suc)) in
    Syn.NRec (tp', read_back_nf size zero, suc', read_back_ne size n)
  | D.Fst ne -> Syn.Fst (read_back_ne size ne)
  | D.Snd ne -> Syn.Snd (read_back_ne size ne)

let rec initial_env env =
  match env with
  | [] -> []
  | t :: env ->
    let env' = initial_env env in
    let d = D.Neutral (eval t env', D.Var (List.length env)) in
    d :: env'

let normalize ~env ~term ~tp =
  let env' = initial_env env in
  let tp' = eval tp env' in
  let term' = eval term env' in
  read_back_nf (List.length env') (D.Normal (tp', term'))
