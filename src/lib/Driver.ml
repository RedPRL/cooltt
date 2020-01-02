module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError

type output =
  | NoOutput of Env.t
  | NormalizedTerm of S.t * S.t
  | NormalizedDef of CS.ident * S.t
  | ElaboratedType of S.tp
  | Quit

let update_env env = 
  function
  | NoOutput env -> env
  | _ -> env

let output = 
  function
  | NoOutput _ -> ()
  | NormalizedTerm (s, t) ->
    Format.fprintf Format.std_formatter "Computed normal form of@ @[<hv>";
    S.pp Format.std_formatter s;
    Format.fprintf Format.std_formatter "@] as @ @[<hv>";
    S.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | NormalizedDef (name, t) ->
    Format.fprintf Format.std_formatter
      "Computed normal form of [%s]:@ @[<hv>" name;
    Syntax.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | ElaboratedType tp ->
    Format.fprintf Format.std_formatter "Elaborated@ @[<hv>";
    S.pp_tp Format.std_formatter tp;
    Format.fprintf Format.std_formatter "@]@,"
  | Quit -> exit 0

let rec int_to_term = 
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module EM = ElabMonad

let rec unravel_spine f = 
  function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs

let rec bind (env : Env.t) = 
  function
  | CS.Var id ->
    begin
      match Env.resolve id env with
      | `Local ix -> S.Var ix
      | `Global sym -> S.Global sym
      | `Unbound -> raise @@ Err.ElabError (UnboundVariable id)
    end
  | CS.Let (tp, B {name; body}) ->
    S.Let (bind env tp, bind (Env.push_name name env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind_ty env tp)
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec {mot = B {name = mot_name; body = mot_body}; zero; suc = B2 {name1 = suc_name1; name2 = suc_name2; body = suc_body}; nat} ->
    S.NRec
      (bind_ty (Env.push_name mot_name env) mot_body,
       bind env zero,
       bind (Env.push_names [suc_name2; suc_name1] env) suc_body,
       bind env nat)
  | CS.Lam (BN {names = []; body}) -> bind env body
  | CS.Lam (BN {names = x :: names; body}) ->
    let lam = CS.Lam (BN {names; body}) in
    S.Lam (bind (Env.push_name x env) lam)
  | CS.Ap (f, args) ->
    List.map (bind_spine env) args |> unravel_spine (bind env f)
  | CS.Pair (l, r) -> S.Pair (bind env l, bind env r)
  | CS.Fst p -> S.Fst (bind env p)
  | CS.Snd p -> S.Snd (bind env p)
  | CS.J {mot = B3 {name1 = left; name2 = right; name3 = prf; body = mot_body}; refl = B {name = refl_name; body = refl_body}; eq} ->
    S.J
      (bind_ty (Env.push_names [prf; right; left] env) mot_body,
       bind (Env.push_name refl_name env) refl_body,
       bind env eq )
  | CS.Refl (Some t) -> S.Refl (bind env t)
  | _ -> failwith "driver expected term"

and bind_ty env = 
  function
  | CS.Sg ([], body) -> bind_ty env body
  | CS.Sg (Cell cell :: tele, body) ->
    S.Sg
      (bind_ty env cell.tp,
       bind_ty (Env.push_name cell.name env) (CS.Sg (tele, body)))
  | CS.Pi ([], body) -> bind_ty env body
  | CS.Pi (Cell cell :: tele, body) ->
    S.Pi
      (bind_ty env cell.tp,
       bind_ty (Env.push_name cell.name env) (CS.Pi (tele, body)))
  | CS.Nat -> S.Nat
  | CS.Id (tp, left, right) ->
    S.Id (bind_ty env tp, bind env left, bind env right)
  | e -> failwith @@ "driver expected tp but found " ^ CS.show e

and bind_spine env = 
  function
  | CS.Term t -> fun f -> S.Ap (f, bind env t)

let process_decl env = 
  function
  | CS.Def {name; def; tp} ->
    let def = bind env def in
    let tp = bind_ty env tp in
    Check.check_tp ~env ~tp;
    let sem_env = Env.to_sem_env env in
    let sem_tp = Nbe.eval_tp tp sem_env in
    Check.check ~env ~term:def ~tp:sem_tp;
    let sem_def = Nbe.eval def sem_env in
    NoOutput (Env.add_top_level name sem_def sem_tp env)
  | CS.NormalizeDef name -> 
    let err = Err.ElabError (UnboundVariable name) in
    begin
      match Env.resolve name env with
      | `Local _ | `Unbound -> raise err
      | `Global sym ->
        let nf = Env.get_global sym env in 
        NormalizedDef (name, Nbe.read_back_nf 0 nf)
    end
  | CS.NormalizeTerm {term; tp} ->
    let term = bind env term in
    let tp = bind_ty env tp in
    Check.check_tp ~env ~tp;
    let sem_env = Env.to_sem_env env in
    let sem_tp = Nbe.eval_tp tp sem_env in
    Check.check ~env ~term ~tp:sem_tp;
    let sem_term = Nbe.eval term sem_env in
    let norm_term =
      Nbe.read_back_nf 0 (D.Nf {term = sem_term; tp = sem_tp})
    in
    NormalizedTerm (term, norm_term)
  | CS.Quit -> Quit
  | CS.ElaborateType tp ->
    begin
      match EM.run (Elaborator.check_tp tp) env with
      | `Ret tp -> ElaboratedType tp
      | `Throw exn -> raise exn
    end

let rec process_sign_loop env = 
  function
  | [] -> ()
  | d :: ds ->
    let o = process_decl env d in
    output o;
    process_sign_loop (update_env env o) ds

let process_sign : ConcreteSyntax.signature -> unit =
  process_sign_loop Env.init