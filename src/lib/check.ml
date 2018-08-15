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

let use_tick i =
  let rec go j = function
    | [] -> []
    | Term {term; tp; is_active; under_lock} :: env ->
      Term {term; tp; is_active = is_active && j > i; under_lock} :: go (j + 1) env
    | Tick {is_active; under_lock} :: env ->
      Tick {is_active = is_active && j > i; under_lock} :: go (j + 1) env in
  go 0

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
  | Syn.Var i -> assert_eq env (get_var env i) tp
  | Let (def, body) ->
    let def_tp = synth ~env ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    let entry = Term {term = def_val; tp = def_tp; is_active = true; under_lock = 0} in
    check ~env:(entry :: env) ~term:body ~tp
  | Check (term, tp') ->
    check ~env ~term ~tp;
    assert_eq env tp (Nbe.eval tp' (env_to_sem_env env))
  | Nat -> assert_uni tp
  | Zero ->
    begin
      match tp with
      | D.Nat -> ()
      | _ -> raise Type_error
    end
  | Suc term ->
    check ~env ~term ~tp:Nat;
    begin
      match tp with
      | D.Nat -> ()
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
    assert_eq env tp (Nbe.eval mot (Nbe.eval n sem_env :: sem_env))
  | _ -> raise Type_error

and synth ~env:_ ~term:_ = failwith "todo"
