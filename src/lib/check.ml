type env_entry =
    Term of {term : Domain.t; tp : Domain.t; under_lock : int; is_active : bool}
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
    | Next t | Later t | Lam t -> go (min + 1) t
    | Let (t1, t2) | Pi (t1, t2) | Sig (t1, t2) | DFix (t1, t2) ->
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

let check ~env:_ ~term:_ ~tp:_ = failwith "todo"
let synth ~env:_ ~term:_ = failwith "todo"
