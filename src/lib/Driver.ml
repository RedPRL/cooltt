module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
open CoolBasis


let _ =
  Printexc.record_backtrace true;
  ()


type message =
  | NormalizedTerm of S.t * S.t

let pp_message fmt =
  function
  | NormalizedTerm (s, t) ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "Computed normal form of@ @[<hv>%a@] as@,@[<hv> %a@]@,"
      (S.pp env) s
      (S.pp env) t

let rec int_to_term =
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module EM = ElabBasics

let elaborate_typed_term name tp tm =
  let open Monad.Notation (EM) in
  EM.push_problem name @@
  let* tp =
    EM.push_problem "tp" @@
    Tactic.Tp.run @@ Elaborator.chk_tp tp
  in
  let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
  let* tm =
    EM.push_problem "tm" @@
    Elaborator.chk_tm tm vtp
  in
  let+ vtm = EM.lift_ev @@ Nbe.eval tm in
  tp, vtp, tm, vtm

let execute_decl =
  let open Monad.Notation (EM) in
  function
  | CS.Def {name; def; tp} ->
    let* _tp, vtp, _tm, vtm = elaborate_typed_term name tp def in
    let+ _sym = EM.add_global (Some name) vtp @@ Some vtm in
    `Continue
  | CS.NormalizeTerm term ->
    EM.veil (Veil.const `Transparent) @@
    let* tm, vtp = Elaborator.syn_tm term in
    let* vtm = EM.lift_ev @@ Nbe.eval tm in
    let* tm' = EM.lift_qu @@ Nbe.quote_con vtp vtm in
    let+ () = EM.emit pp_message @@ NormalizedTerm (tm, tm') in
    `Continue
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
  EM.run_exn ElabState.init Env.init @@
  execute_signature sign

