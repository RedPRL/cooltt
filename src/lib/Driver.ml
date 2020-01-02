module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError

type output =
  | NoOutput of Env.t
  | NormalizedTerm of S.t * S.t
  | NormalizedDef of CS.ident * S.t
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
    S.pp Format.std_formatter t;
    Format.fprintf Format.std_formatter "@]@,"
  | Quit -> exit 0

let rec int_to_term = 
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module EM = ElabMonad

let elaborate_typed_term tp tm = 
  let open Monad.Notation (EM) in
  let* tp = Elaborator.check_tp tp in
  let* vtp = Elaborator.eval_tp tp in
  let* tm = Elaborator.check_tm tm vtp in
  let+ vtm = Elaborator.eval_tm tm in
  tp, vtp, tm, vtm

let process_decl env = 
  function
  | CS.Def {name; def; tp} ->
    let script = elaborate_typed_term tp def in
    begin
      match EM.run script env with
      | `Ret (_, vtp, _, vtm) -> NoOutput (Env.add_top_level name vtm vtp env)
      | `Throw exn -> raise exn
    end
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
    let script = elaborate_typed_term tp term in
    begin
      match EM.run script env with
      | `Ret (_, vtp, tm, vtm) -> 
        let norm_term = Nbe.read_back_nf 0 (D.Nf {term = vtm; tp = vtp}) in
        NormalizedTerm (tm, norm_term)
      | `Throw exn -> raise exn
    end
  | CS.Quit -> Quit

let rec process_sign_loop env = 
  function
  | [] -> ()
  | d :: ds ->
    let o = process_decl env d in
    output o;
    process_sign_loop (update_env env o) ds

let process_sign : ConcreteSyntax.signature -> unit =
  process_sign_loop Env.init