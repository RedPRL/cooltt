module CS = ConcreteSyntax
module S = Syntax
module D = Domain

type error = 
  | Unbound_variable of CS.ident
  | InvalidTypeExpression of CS.t 

exception ElabError of error

module Env : sig
  type t
  val init : t
  val bindings : t -> CS.ident list
  val check_env : t -> Check.Env.t
  val push_name : CS.ident -> t -> t
  val push_names : CS.ident list -> t -> t
  val find_idx : CS.ident -> t -> int
  val add_entry : Check.Env.entry -> t -> t
end = 
struct
  type t = {check_env : Check.env; bindings : string list}
  let init = {check_env = Check.Env.empty; bindings = []}
  let bindings {bindings; _} = bindings
  let check_env {check_env; _} = check_env
  let push_name i env = {env with bindings = i :: env.bindings }
  let push_names is env = {env with bindings = is @ env.bindings }

  let find_idx key env =
    let rec go i = 
      function
      | [] -> raise @@ ElabError (Unbound_variable key)
      | x :: xs -> if String.equal x key then i else go (i + 1) xs 
    in
    go 0 @@ bindings env

  let add_entry e env = 
    {env with check_env = Check.Env.add_entry e env.check_env}
end


type output =
    NoOutput of Env.t
  | NF_term of S.t * S.t
  | NF_def of CS.ident * S.t
  | Elaborated_type of S.tp
  | Quit

let update_env env = 
  function
  | NoOutput env -> env
  | _ -> env

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
  | Elaborated_type tp ->
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
  val check : CS.t -> D.tp -> S.t EM.m
end = 
struct
  open Monad.Notation (EM)

  let eval_tp tp = 
    let* env = EM.read in 
    let chk_env = Env.check_env env in
    let sem_env = Check.Env.to_sem_env chk_env in
    match Nbe.eval_tp tp sem_env with
    | v -> EM.ret v
    | exception exn -> 
      EM.throw exn

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
    | _ -> failwith "TODO"

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
      
  and check _cs _tp = failwith ""
end

let rec bind (env : Env.t) = 
  function
  | CS.Var i -> S.Var (Env.find_idx i env)
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
  | CS.Refl t -> 
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
      match Check.Env.get_entry (Env.check_env env) (Env.find_idx name env) with
      | Check.Env.TopLevel {term; tp} -> NF_def (name, Nbe.read_back_nf 0 (D.Nf {term; tp}))
      | _ -> raise err
      | exception Failure _ -> raise err
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
    NF_term (term, norm_term)
  | CS.Quit -> Quit
  | CS.ElaborateType tp ->
    begin
      match EM.run (Elaborator.check_tp tp) env with
      | `Ret tp ->
        Elaborated_type tp
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
