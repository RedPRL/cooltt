module CS = Concrete_syntax
module S = Syntax
module D = Domain

type env = Env of {size : int; check_env : Check.env; bindings : string list}

type output =
    NoOutput of env
  | NF of D.t
  | Quit

let update_env env = function
  | NoOutput env -> env
  | NF _ -> env
  | Quit -> env

let output = function
  | NoOutput _ -> ()
  | NF t -> Printf.printf "Computed normal form:\n%s" (D.pp t)
  | Quit -> exit 0

let find_idx key =
  let rec go i = function
    | [] -> raise (Failure "Improper binding structure in driver.ml")
    | x :: xs -> if String.equal x key then i else go (i + 1) xs in
  go 0

let rec int_to_term = function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

let rec unravel_spine f = function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec bind env = function
  | CS.Var i -> S.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    S.Let (bind env tp, bind (name :: env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind env tp)
  | CS.Nat -> S.Nat
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = Binder {name = mot_name; body = mot_body};
        zero;
        suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat} ->
    S.NRec
      (bind (mot_name :: env) mot_body,
       bind env zero,
       bind (suc_name2 :: suc_name1 :: env) suc_body,
       bind env nat)
  | CS.Pi (tp, Binder {name; body}) ->
    S.Pi (bind env tp, bind (name :: env) body)
  | CS.Lam (tp, Binder {name; body}) ->
    S.Lam (bind env tp, bind (name :: env) body)
  | CS.Ap (f, args) ->
    List.map (bind_spine env) args |> unravel_spine (bind env f)
  | CS.Sig (tp, Binder {name; body}) ->
    S.Sig (bind env tp, bind (name :: env) body)
  | CS.Pair (l, r) -> S.Pair (bind env l, bind env r)
  | CS.Fst p -> S.Fst (bind env p)
  | CS.Snd p -> S.Snd (bind env p)
  | CS.Later (Binder {name; body}) -> S.Later (bind (name :: env) body)
  | CS.Next (Binder {name; body}) -> S.Next (bind (name :: env) body)
  | CS.Bullet -> S.Bullet
  | CS.Box t -> S.Box (bind env t)
  | CS.Shut t -> S.Shut (bind env t)
  | CS.Open t -> S.Open (bind env t)
  | CS.DFix (tp, Binder {name; body}) ->
    S.DFix (bind env tp, bind (name :: env) body)
  | CS.Fold {uni; idx_tp; fix_body = Binder {name; body}; idx; term; tick} ->
    S.Fold
      (uni,
       bind env idx_tp,
       bind (name :: env) body,
       bind env idx,
       bind env term,
       bind env tick)
  | CS.Unfold {uni; idx_tp; fix_body = Binder {name; body}; idx; term; tick} ->
    S.Unfold
      (uni,
       bind env idx_tp,
       bind (name :: env) body,
       bind env idx,
       bind env term,
       bind env tick)
  | CS.Uni i -> S.Uni i

and bind_spine env = function
  | CS.Term t -> fun f -> S.Ap (f, bind env t)
  | CS.Tick t -> fun f -> S.Prev (f, bind env t)

let process_decl (Env {size; check_env; bindings})  = function
  | CS.Def {name; def; tp} ->
    let def = bind bindings def in
    let tp = bind bindings tp in
    Check.check_tp ~size ~env:check_env ~term:def;
    let sem_env = Check.env_to_sem_env size check_env in
    let sem_tp = Nbe.eval tp sem_env in
    Check.check ~size ~env:check_env ~term:def ~tp:sem_tp;
    let sem_def = Nbe.eval def sem_env in
    let new_entry = Check.Term {term = sem_def; tp = sem_tp; locks = 0; is_active = true} in
    NoOutput (Env {size = size + 1; check_env = new_entry :: check_env; bindings = name :: bindings })
  | CS.NormalizeDef _ -> failwith "todo"
  | CS.NormalizeTerm _ -> failwith "todo"
  | CS.Quit -> Quit
