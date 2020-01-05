module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError

type message =
  | NormalizedTerm of S.t * S.t
  | NormalizedDef of CS.ident * S.t

let pp_message fmt = 
  function
  | NormalizedTerm (s, t) ->
    Format.fprintf fmt "Computed normal form of@ @[<hv>";
    S.pp fmt s;
    Format.fprintf fmt "@] as @ @[<hv>";
    S.pp fmt t;
    Format.fprintf fmt "@]@,"
  | NormalizedDef (name, t) ->
    Format.fprintf fmt
      "Computed normal form of [%s]:@ @[<hv>" name;
    S.pp fmt t;
    Format.fprintf fmt "@]@,"

let rec int_to_term = 
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module EM = 
struct 
  include ElabMonad
  include ElabBasics 
end

let elaborate_typed_term tp tm = 
  let open Monad.Notation (EM) in
  let* tp = Elaborator.check_tp tp in
  let* vtp = EM.lift_ev @@ Nbe.Monadic.eval_tp tp in 
  let* tm = Elaborator.check_tm tm vtp in
  let+ vtm = EM.lift_ev @@ Nbe.Monadic.eval tm in
  tp, vtp, tm, vtm

let execute_decl =
  let open Monad.Notation (EM) in 
  function
  | CS.Def {name; def; tp} ->
    let* _tp, vtp, _tm, vtm = elaborate_typed_term tp def in
    let* _ = EM.add_global (Some name) vtp @@ Some vtm in
    EM.ret `Continue
  | CS.NormalizeDef name ->
    let* res = EM.resolve name in
    begin
      match res with
      | `Global sym ->
        let* D.Nf nf = EM.get_global sym in
        let* tm = EM.lift_qu @@ Nbe.Monadic.quote nf.tp nf.el in
        let* () = EM.emit pp_message @@ NormalizedDef (name, tm) in
        EM.ret `Continue
      | _ -> 
        EM.throw @@ Err.ElabError (UnboundVariable name)
    end
  | CS.NormalizeTerm {term; tp} ->
    let* _, vtp, tm, vtm = elaborate_typed_term tp term in
    let* tm' = EM.lift_qu @@ Nbe.Monadic.quote vtp vtm in
    let* () = EM.emit pp_message @@ NormalizedTerm (tm, tm') in 
    EM.ret `Continue
  | CS.Quit -> 
    EM.ret `Quit

let rec execute_signature sign =
  let open Monad.Notation (EM) in 
  match sign with 
  | [] -> EM.ret ()
  | d :: sign ->
    let* res = execute_decl d in 
    match res with 
    | `Continue -> 
      execute_signature sign
    | `Quit ->
      EM.ret ()

let process_sign : CS.signature -> unit =
  fun sign ->
  match EM.run (execute_signature sign) Env.init with
  | EM.Ret () -> ()
  | EM.Throw exn -> raise exn