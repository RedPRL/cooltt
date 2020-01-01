module CS = ConcreteSyntax
module S = Syntax
module D = Domain

type error = 
  | Unbound_variable of CS.ident
  | ExpectedEqual of D.tp * D.t * D.t
  | ExpectedEqualTypes of D.tp * D.tp
  | InvalidTypeExpression of CS.t 
  | ExpectedPiType of D.tp

exception ElabError of error

module Env = ElabEnv


type output =
    NoOutput of Env.t
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
    Format.fprintf Format.std_formatter "Computed normal form of [%s]:@ @[<hv>" name;
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

let rec unravel_spine f = 
  function
  | [] -> f
  | x :: xs -> unravel_spine (x f) xs


(* experimental *)
module ElabMonad : 
sig 
  include Monad.S
  val read : Env.t m
  val throw : exn -> 'a m
  val run : 'a m -> Env.t -> [`Ret of 'a | `Throw of exn]

  val push_var : CS.ident -> D.tp -> 'a m -> 'a m
end =
struct
  type 'a m = Env.t -> [`Ret of 'a | `Throw of exn]

  let read env = `Ret env
  let throw exn _env = `Throw exn
  let run m env = m env

  let ret a _env = `Ret a
  let bind m k = 
    fun env ->
    match m env with 
    | `Ret a ->
      k a env
    | `Throw exn ->
      `Throw exn

  let push_var id tp m = 
    fun env ->
    let var = D.Var (Check.Env.size @@ Env.check_env env) in
    let term = D.Neutral {term = var; tp} in 
    let entry = Check.Env.Term {term; tp} in
    let env' = Env.add_entry entry @@ Env.push_name id env in 
    m env'
end

module EM = ElabMonad

module Elaborator : 
sig 
  val check_tp : CS.t -> S.tp EM.m
  val check_tm : CS.t -> D.tp -> S.t EM.m
end = 
struct
  open Monad.Notation (EM)

  let read_check_env = 
    let+ env = EM.read in 
    Env.check_env env

  let read_sem_env = 
    let+ chk_env = read_check_env in
    Check.Env.to_sem_env chk_env

  let eval_tp tp = 
    let* sem_env = read_sem_env in 
    match Nbe.eval_tp tp sem_env with
    | v -> EM.ret v
    | exception exn -> 
      EM.throw exn

  let eval_tm tp = 
    let* sem_env = read_sem_env in 
    match Nbe.eval tp sem_env with
    | v -> EM.ret v
    | exception exn -> 
      EM.throw exn

  let inst_tp_clo clo v =
    match Nbe.do_tp_clo clo v with
    | v -> EM.ret v
    | exception exn ->
      EM.throw exn

  let equate tp l r = 
    let* env = read_check_env in 
    match Nbe.equal_nf (Check.Env.size env) (D.Nf {tp; term = l}) (D.Nf {tp; term = r}) with
    | true -> EM.ret ()
    | false -> EM.throw @@ ElabError (ExpectedEqual (tp, l, r))

  let equate_tp tp tp' = 
    let* env = read_check_env in 
    match Nbe.equal_tp (Check.Env.size env) tp tp' with
    | true -> EM.ret ()
    | false -> EM.throw @@ ElabError (ExpectedEqualTypes (tp, tp'))

  let quote tp v =
    let* env = read_check_env in 
    match Nbe.read_back_nf (Check.Env.size env) @@ D.Nf {tp; term = v} with
    | t -> EM.ret t
    | exception exn -> EM.throw exn

  let lookup_var id = 
    let* env = EM.read in
    match Env.find_ix id env with
    | Some ix -> 
      let chk_env = Env.check_env env in
      let tp = Check.Env.get_var chk_env ix in
      EM.ret (S.Var ix, tp)
    | None -> 
      EM.throw @@ ElabError (Unbound_variable id)


  let dest_pi =
    function
    | D.Pi (base, fam) ->
      EM.ret (base, fam)
    | tp ->
      EM.throw @@ ElabError (ExpectedPiType tp)

  let rec check_tp : CS.t -> S.tp EM.m = 
    function
    | CS.Pi (cells, body) ->
      check_pi_tp cells body
    | CS.Sg (cells, body) ->
      check_sg_tp cells body
    | CS.Nat ->
      EM.ret S.Nat
    | CS.Id (tp, l, r) ->
      let* tp = check_tp tp in
      let* vtp = eval_tp tp in
      let+ l = check_tm l vtp
      and+ r = check_tm r vtp in
      S.Id (tp, l, r)
    | tp -> 
      EM.throw @@ ElabError (InvalidTypeExpression tp)

  and check_tm : CS.t -> D.tp -> S.t EM.m =
    fun cs tp ->
    match cs, tp with
    | CS.Refl _, D.Id (tp, l, r) ->
      let+ () = equate tp l r
      and+ t = quote tp l in
      S.Refl t
    | CS.Lit n, D.Nat ->
      EM.ret @@ int_to_term n
    | _ ->
      let* tm, tp' = synth_tm cs in 
      let+ () = equate_tp tp tp' in
      tm

  and synth_tm : CS.t -> (S.t * D.tp) EM.m = 
    function
    | CS.Var id -> 
      lookup_var id
    | CS.Ap (t, ts) ->
      let* t, tp = synth_tm t in
      synth_ap t tp ts
    | _ ->
      failwith "TODO"

  and synth_ap head head_tp spine = 
    match spine with
    | [] -> EM.ret (head, head_tp)
    | CS.Term arg :: spine ->
      let* base, fam = dest_pi head_tp in 
      let* arg = check_tm arg base in
      let* varg = eval_tm arg in
      let* fib = inst_tp_clo fam varg in
      synth_ap (S.Ap (head, arg)) fib spine

  and check_sg_tp cells body =
    match cells with
    | [] -> check_tp body
    | Cell cell :: cells ->
      let* base = check_tp cell.tp in
      let* vbase = eval_tp base in
      let+ fam =
        EM.push_var cell.name vbase @@ 
        check_sg_tp cells body 
      in 
      S.Sg (base, fam)
      
  and check_pi_tp cells body =
    match cells with
    | [] -> check_tp body
    | Cell cell :: cells ->
      let* base = check_tp cell.tp in
      let* vbase = eval_tp base in
      let+ fam =
        EM.push_var cell.name vbase @@ 
        check_pi_tp cells body 
      in 
      S.Pi (base, fam)
end

let rec bind (env : Env.t) = 
  function
  | CS.Var id -> 
    begin
      match Env.find_ix id env with
      | Some ix -> S.Var ix
      | None -> raise @@ ElabError (Unbound_variable id)
    end
  | CS.Let (tp, B {name; body}) ->
    S.Let (bind env tp, bind (Env.push_name name env) body)
  | CS.Check {term; tp} -> S.Check (bind env term, bind_ty env tp)
  | CS.Suc t -> S.Suc (bind env t)
  | CS.Lit i -> int_to_term i
  | CS.NRec
      { mot = B {name = mot_name; body = mot_body};
        zero;
        suc = B2 {name1 = suc_name1; name2 = suc_name2; body = suc_body};
        nat} ->
    S.NRec
      (bind_ty (Env.push_name mot_name env) mot_body,
       bind env zero,
       bind (Env.push_names [suc_name2;suc_name1] env) suc_body,
       bind env nat)
  | CS.Lam (BN {names = []; body}) ->
    bind env body
  | CS.Lam (BN {names = x :: names; body}) ->
    let lam = CS.Lam (BN {names; body}) in
    S.Lam (bind (Env.push_name x env) lam)
  | CS.Ap (f, args) ->
    List.map (bind_spine env) args |> unravel_spine (bind env f)
  | CS.Pair (l, r) -> S.Pair (bind env l, bind env r)
  | CS.Fst p -> S.Fst (bind env p)
  | CS.Snd p -> S.Snd (bind env p)
  | CS.J
      {mot = B3 {name1 = left; name2 = right; name3 = prf; body = mot_body};
       refl = B {name = refl_name; body = refl_body};
       eq} ->
    S.J
      (bind_ty (Env.push_names [prf; right; left] env) mot_body,
       bind (Env.push_name refl_name env) refl_body,
       bind env eq)
  | CS.Refl (Some t) -> 
    S.Refl (bind env t)
  | _ -> failwith "driver expected term"

and bind_ty env =
  function
  | CS.Sg ([], body) ->
    bind_ty env body
  | CS.Sg (Cell cell :: tele, body) ->
    S.Sg (bind_ty env cell.tp, bind_ty (Env.push_name cell.name env) (CS.Sg (tele, body)))
  | CS.Pi ([], body) ->
    bind_ty env body
  | CS.Pi (Cell cell :: tele, body) ->
    S.Pi (bind_ty env cell.tp, bind_ty (Env.push_name cell.name env) (CS.Pi (tele, body)))
  | CS.Nat -> S.Nat
  | CS.Id (tp, left, right) ->
    S.Id (bind_ty env tp, bind env left, bind env right)
  | e -> 
    failwith @@ "driver expected tp but found "  ^ CS.show e

and bind_spine env = 
  function
  | CS.Term t -> fun f -> S.Ap (f, bind env t)

let process_decl env = 
  function
  | CS.Def {name; def; tp} ->
    let def = bind env def in
    let tp = bind_ty env tp in
    let check_env = Env.check_env env in
    Check.check_tp ~env:check_env ~tp;
    let sem_env = Check.Env.to_sem_env check_env in
    let sem_tp = Nbe.eval_tp tp sem_env in
    Check.check ~env:check_env ~term:def ~tp:sem_tp;
    let sem_def = Nbe.eval def sem_env in
    let new_entry = Check.Env.TopLevel {term = sem_def; tp = sem_tp} in
    NoOutput (Env.add_entry new_entry @@ Env.push_name name env)
  | CS.NormalizeDef name ->
    let err = ElabError (Unbound_variable name) in 
    begin
      match Env.find_ix name env with
      | None -> raise err
      | Some ix ->
        match Check.Env.get_entry (Env.check_env env) ix with
        | Check.Env.TopLevel {term; tp} -> NormalizedDef (name, Nbe.read_back_nf 0 (D.Nf {term; tp}))
        | _ -> raise err
    end
  | CS.NormalizeTerm {term; tp} ->
    let term = bind env term in
    let tp = bind_ty env tp in
    let check_env = Env.check_env env in
    Check.check_tp ~env:check_env ~tp;
    let sem_env = Check.Env.to_sem_env check_env in 
    let sem_tp = Nbe.eval_tp tp sem_env in
    Check.check ~env:check_env ~term ~tp:sem_tp;
    let sem_term = Nbe.eval term sem_env in
    let norm_term = Nbe.read_back_nf 0 (D.Nf {term = sem_term; tp = sem_tp}) in
    NormalizedTerm (term, norm_term)
  | CS.Quit -> Quit
  | CS.ElaborateType tp ->
    begin
      match EM.run (Elaborator.check_tp tp) env with
      | `Ret tp ->
        ElaboratedType tp
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
