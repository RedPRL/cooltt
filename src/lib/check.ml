module D = Domain
module Syn = Syntax
type env_entry =
    Term of {term : D.t; tp : D.t; under_lock : int; is_active : bool}
  | Tick of {under_lock : int; is_active : bool}
type env = env_entry list

exception Type_error
exception Cannot_synth

let env_to_sem_env env =
  let size = List.length env in
  let rec go i = function
    | [] -> []
    | Term {term; _} :: env -> term :: go (i + 1) env
    | Tick _ :: env -> Tick (size - (i + 1)) :: go (i + 1) env in
  go 0 env

module S = Set.Make(struct type t = int;; let compare = compare end)

let free_vars =
  let open Syntax in
  let rec go min = function
    | Var i -> if min < i then S.singleton (i - min) else S.empty
    | Next t | Later t -> go (min + 1) t
    | Lam (t1, t2) | Let (t1, t2) | Pi (t1, t2) | Sig (t1, t2) | DFix (t1, t2) ->
      S.union (go min t1) (go (min + 1) t2)
    | Pair (t1, t2) | Check (t1, t2) | Ap (t1, t2) | Prev (t1, t2) -> S.union (go min t1) (go min t2)
    | Nat | Zero | Uni _ | Bullet -> S.empty
    | Suc t | Box t | Open t | Shut t | Fst t | Snd t -> go min t
    | NRec (m, zero, suc, n) ->
      go (min + 1) m
      |> S.union (go min zero)
      |> S.union (go (min + 2) suc)
      |> S.union (go min n) in
  go 0

let strip_env support =
  let rec delete_n_locks locks = function
    | [] -> []
    | Term {term; tp; is_active; under_lock} :: env ->
      Term {term; tp; is_active; under_lock = under_lock - locks} ::
      delete_n_locks locks env
    | Tick {under_lock; is_active} :: env ->
      Tick {under_lock = under_lock - locks ; is_active} ::
      delete_n_locks locks env in
  let rec go i = function
    | [] -> []
    | Term {term; tp; is_active; _} :: env ->
      Term {term; tp; is_active; under_lock = 0} :: go (i + 1) env
    | Tick {under_lock; is_active} :: env ->
      if S.mem i support
      (* Cannot weaken this tick! *)
      then Tick {under_lock = 0; is_active} :: delete_n_locks under_lock env
      else Tick {under_lock = 0; is_active = false} :: go (i + 1) env in
  go 0

let use_tick env i =
  let rec go j = function
    | [] -> []
    | Term {term; tp; is_active; under_lock} :: env ->
      Term {term; tp; is_active = is_active && j > i; under_lock} :: go (j + 1) env
    | Tick {is_active; under_lock} :: env ->
      Tick {is_active = is_active && j > i; under_lock} :: go (j + 1) env in
  go 0 env

let apply_lock =
  List.map
    (function
      | Tick t -> Tick {t with under_lock = t.under_lock + 1}
      | Term t -> Term {t with under_lock = t.under_lock + 1})

let get_var env n = match List.nth env n with
  | Term {term = _; tp; under_lock = 0; is_active = true} -> tp
  | Term _ -> raise Type_error
  | Tick _ -> raise Type_error

let get_tick env n = match List.nth env n with
  | Tick {under_lock = 0; is_active = true} -> ()
  | Term _ -> raise Type_error
  | Tick _ -> raise Type_error

let assert_eq env t1 t2 =
  let sem_env = env_to_sem_env env in
  if Nbe.equal sem_env t1 t2 then () else raise Type_error

let assert_uni = function
  | D.Uni _ -> ()
  | _ -> raise Type_error

let rec check ~env ~term ~tp = match term with
  | Syn.Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    let entry = Term {term = def_val; tp = def_tp; is_active = true; under_lock = 0} in
    check ~env:(entry :: env) ~term:body ~tp
  | Nat -> assert_uni tp
  | Pi (src, dest) | Sig (src, dest) ->
    check ~env ~term:src ~tp;
    let src_sem = Nbe.eval src (env_to_sem_env env) in
    let var = D.mk_var tp (List.length env) in
    let src_entry = Term {term = var; tp = src_sem; is_active = true; under_lock = 0} in
    check ~env:(src_entry :: env) ~term:dest ~tp
  | Lam (arg_tp, body) ->
    assert_uni (synth ~env ~term:arg_tp);
    let arg_tp_sem = Nbe.eval arg_tp (env_to_sem_env env) in
    let var = D.mk_var arg_tp_sem (List.length env) in
    let arg_entry = Term {term = var; tp = arg_tp_sem; is_active = true; under_lock = 0} in
    begin
      match tp with
      | D.Pi (given_arg_tp, dest_tp) ->
        check ~env:(arg_entry :: env) ~term:body ~tp:(Nbe.do_clos dest_tp var);
        assert_eq env given_arg_tp arg_tp_sem
      | _ -> raise Type_error
    end
  | Pair (left, right) ->
    begin
      match tp with
      | D.Sig (left_tp, right_tp) ->
        check ~env ~term:left ~tp:left_tp;
        let left_sem = Nbe.eval left (env_to_sem_env env) in
        check ~env ~term:right ~tp:(Nbe.do_clos right_tp left_sem)
      | _ -> raise Type_error
    end
  | Later t ->
    check ~env:(Tick {is_active = true; under_lock = 0} :: env) ~term:t ~tp
  | Next t ->
    begin
      match tp with
      | Next clos ->
        let tp = Nbe.do_tick_clos clos (Tick (List.length env)) in
        check ~env:(Tick {is_active = true; under_lock = 0} :: env) ~term:t ~tp
      | _ -> raise Type_error
    end
  | Box term -> check ~env:(apply_lock env) ~term ~tp
  | Shut term ->
    begin
      match tp with
      | Box tp -> check ~env:(apply_lock env) ~term ~tp
      | _ -> raise Type_error
    end
  | Uni i ->
    begin
      match tp with
      | Uni j when i < j -> ()
      | _ -> raise Type_error
    end
  | Bullet -> raise Type_error
  | term -> assert_eq env (synth ~env ~term) tp

and synth ~env ~term =
  match term with
  | Syn.Var i -> get_var env i
  | Check (term, tp') ->
    let tp = synth ~env ~term in
    assert_eq env tp (Nbe.eval tp' (env_to_sem_env env));
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~term ~tp:Nat; D.Nat
  | Fst p ->
    begin
      match synth ~env ~term:p with
      | Sig (left_tp, _) -> left_tp
      | _ -> raise Type_error
    end
  | Snd p ->
    begin
      match synth ~env ~term:p with
      | Sig (_, right_tp) ->
        let proj = Nbe.eval (Fst p) (env_to_sem_env env) in
        Nbe.do_clos right_tp proj
      | _ -> raise Type_error
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~term:f with
      | Pi (src, dest) ->
        check ~env ~term:a ~tp:src;
        let a_sem = Nbe.eval a (env_to_sem_env env) in
        Nbe.do_clos dest a_sem
      | _ -> raise Type_error
    end
  | Prev (term, tick) ->
    begin
      match tick with
      | Var i ->
        get_tick env i;
        let i' = List.length env - (i + 1) in
        begin
          match synth ~env:(use_tick env i) ~term with
          | Next clos -> Nbe.do_tick_clos clos (Tick i')
          | _ -> raise Type_error
        end
      | Bullet ->
        begin
          match synth ~env:(apply_lock env) ~term with
          | Next clos -> Nbe.do_tick_clos clos Bullet
          | _ -> raise Type_error
        end
      | _ -> raise Type_error
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~term:n ~tp:Nat;
    let size = List.length env in
    let var = D.mk_var Nat size in
    let n_entry = Term {term = var; tp = Nat; is_active = true; under_lock = 0} in
    assert_uni (synth ~env:(n_entry :: env) ~term:mot);
    let sem_env = env_to_sem_env env in
    let zero_tp = Nbe.eval mot (Zero :: sem_env) in
    let ih_tp = Nbe.eval mot (Suc var :: sem_env) in
    let suc_tp = Nbe.eval mot (Suc var :: sem_env) in
    let ih_entry = Term {term = D.mk_var ih_tp (size + 1); tp = ih_tp; is_active = true; under_lock = 0} in
    check ~env ~term:zero ~tp:zero_tp;
    check ~env:(ih_entry :: n_entry :: env) ~term:suc ~tp:suc_tp;
    Nbe.eval mot (Nbe.eval n sem_env :: sem_env)
  | Open term ->
    let support = free_vars term in
    let env = strip_env support env in
    begin
      match synth ~env ~term with
      | Box tp -> tp
      | _ -> raise Type_error
    end
  | DFix (tp', body) ->
    let tp'_sem = Nbe.eval tp' (env_to_sem_env env) in
    let next_tp'_sem = D.Next (ConstTickClos tp'_sem) in
    let var = D.mk_var next_tp'_sem (List.length env) in
    let entry = Term {term = var; tp = next_tp'_sem; under_lock = 0; is_active = true} in
    check ~env:(entry :: env) ~term:body ~tp:tp'_sem;
    next_tp'_sem
  | _ -> raise Cannot_synth
