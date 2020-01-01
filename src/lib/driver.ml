module CS = Concrete_syntax
module S = Syntax
module D = Domain

type env = Env of {check_env : Check.env; bindings : string list}

let initial_env = Env {check_env = Check.Env.empty ; bindings = []}

type output =
    NoOutput of env
  | NF_term of S.t * S.t
  | NF_def of CS.ident * S.t
  | Quit

let update_env env = 
  function
  | NoOutput env -> env
  | NF_term _ | NF_def _ | Quit -> env

let output = 
  function
  | NoOutput _ -> ()
  | NF_term (s, t) ->
    Format.fprintf Format.std_formatter "Computed normal form of@ @[<hv>";
    S.pp Format.std_formatter s;
    Format.fprintf Format.std_formatter "@] as @ @[<hv>";
    S.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | NF_def (name, t) ->
    Format.fprintf Format.std_formatter "Computed normal form of [%s]:@ @[<hv>" name;
    Syntax.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | Quit -> exit 0

let find_idx key =
  let rec go i = 
    function
    | [] -> raise (Check.Type_error (Check.Misc ("Unbound variable: " ^ key)))
    | x :: xs -> if String.equal x key then i else go (i + 1) xs in
  go 0

let rec int_to_term = 
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

let rec unravel_spine f = 
  function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec bind env = 
  function
  | CS.Var i -> S.Var (find_idx i env)
  | CS.Let (tp, Binder {name; body}) ->
    S.Let (bind env tp, bind (name :: env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind_ty env tp)
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = Binder {name = mot_name; body = mot_body};
        zero;
        suc = Binder2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat} ->
    S.NRec
      (bind_ty (mot_name :: env) mot_body,
       bind env zero,
       bind (suc_name2 :: suc_name1 :: env) suc_body,
       bind env nat)
  | CS.Lam (BinderN {names = []; body}) ->
    bind env body
  | CS.Lam (BinderN {names = x :: names; body}) ->
    let lam = CS.Lam (BinderN {names; body}) in
    S.Lam (bind (x :: env) lam)
  | CS.Ap (f, args) ->
    List.map (bind_spine env) args |> unravel_spine (bind env f)
  | CS.Pair (l, r) -> S.Pair (bind env l, bind env r)
  | CS.Fst p -> S.Fst (bind env p)
  | CS.Snd p -> S.Snd (bind env p)
  | CS.J
      {mot = Binder3 {name1 = left; name2 = right; name3 = prf; body = mot_body};
       refl = Binder {name = refl_name; body = refl_body};
       eq} ->
    S.J
      (bind_ty (prf :: right :: left :: env) mot_body,
       bind (refl_name :: env) refl_body,
       bind env eq)
  | CS.Refl t -> S.Refl (bind env t)
  | _ -> failwith "driver expected term"

and bind_ty env =
  function
  | CS.Sg ([], body) ->
    bind_ty env body
  | CS.Sg (Cell cell :: tele, body) ->
    S.Sg (bind_ty env cell.tp, bind_ty (cell.name :: env) (CS.Sg (tele, body)))
  | CS.Pi ([], body) ->
    bind_ty env body
  | CS.Pi (Cell cell :: tele, body) ->
    S.Pi (bind_ty env cell.tp, bind_ty (cell.name :: env) (CS.Pi (tele, body)))
  | CS.Nat -> S.Nat
  | CS.Id (tp, left, right) ->
    S.Id (bind_ty env tp, bind env left, bind env right)
  | CS.Ap (f, []) ->
    bind_ty env f
  | e -> 
    failwith @@ "driver expected tp but found "  ^ CS.show e

and bind_spine env = 
  function
  | CS.Term t -> fun f -> S.Ap (f, bind env t)

let process_decl (Env {check_env; bindings}) = 
  function
  | CS.Def {name; def; tp} ->
    let def = bind bindings def in
    let tp = bind_ty bindings tp in
    Check.check_tp ~env:check_env ~tp;
    let sem_env = Check.Env.to_sem_env check_env in
    let sem_tp = Nbe.eval_tp tp sem_env in
    Check.check ~env:check_env ~term:def ~tp:sem_tp;
    let sem_def = Nbe.eval def sem_env in
    let new_entry = Check.Env.TopLevel {term = sem_def; tp = sem_tp} in
    NoOutput (Env {check_env = Check.Env.add_entry new_entry check_env; bindings = name :: bindings })
  | CS.NormalizeDef name ->
    let err = Check.Type_error (Check.Misc ("Unbound variable: " ^ name)) in
    begin
      match Check.Env.get_entry check_env (find_idx name bindings) with
      | Check.Env.TopLevel {term; tp} -> NF_def (name, Nbe.read_back_nf 0 (D.Nf {term; tp}))
      | _ -> raise err
      | exception Failure _ -> raise err
    end
  | CS.NormalizeTerm {term; tp} ->
    let term = bind bindings term in
    let tp = bind_ty bindings tp in
    Check.check_tp ~env:check_env ~tp;
    let sem_env = Check.Env.to_sem_env check_env in
    let sem_tp = Nbe.eval_tp tp sem_env in
    Check.check ~env:check_env ~term ~tp:sem_tp;
    let sem_term = Nbe.eval term sem_env in
    let norm_term = Nbe.read_back_nf 0 (D.Nf {term = sem_term; tp = sem_tp}) in
    NF_term (term, norm_term)
  | CS.Quit -> Quit

let rec process_sign ?env = 
  function
  | [] -> ()
  | d :: ds ->
    let env = match env with
        None -> initial_env
      | Some e -> e in
    let o = process_decl env d in
    output o;
    process_sign ?env:(Some (update_env env o)) ds

let process_sign : Concrete_syntax.signature -> unit = process_sign
