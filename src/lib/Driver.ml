module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module Sem = Semantics
module Qu = Quote
open CoolBasis


let _ =
  Printexc.record_backtrace true;
  ()


type message =
  | NormalizedTerm of {orig : S.t; nf : S.t}
  | TermNotSynthesizable of CS.con_
  | Definition of {ident : Ident.t; tp : S.tp; tm : S.t option}
  | UnboundIdent of Ident.t

let pp_message fmt =
  function
  | NormalizedTerm {orig; nf} ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[Computed normal form of@ @[<hv>%a@] as@,@[<hv> %a@]@]@."
      (S.pp env) orig
      (S.pp env) nf
  | TermNotSynthesizable orig ->
    Format.fprintf fmt
      "@[Please annotate the type of@,@[<hv> %a@]@]@."
      CS.pp_con_ orig
  | Definition {ident; tp; tm = Some tm} ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[<v>%a@ : %a@ = %a@]@."
      Ident.pp ident
      (S.pp_atomic_tp env) tp
      (S.pp_atomic env) tm
  | Definition {ident; tp; tm = None} ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[%a : %a@]@."
      Ident.pp ident
      (S.pp_atomic_tp env) tp
  | UnboundIdent ident ->
    Format.fprintf fmt
      "@[Unbound identifier %a@]@."
      Ident.pp ident

module EM = ElabBasics

let elaborate_typed_term name (args : CS.cell list) tp tm =
  let open Monad.Notation (EM) in
  EM.push_problem name @@
  let* tp =
    EM.push_problem "tp" @@
    Tactic.Tp.run @@ Elaborator.chk_tp_in_tele args tp
  in
  let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
  let* tm =
    EM.push_problem "tm" @@
    Elaborator.chk_tm_in_tele args tm vtp
  in
  let+ vtm = EM.lift_ev @@ Sem.eval tm in
  tp, vtp, tm, vtm

let execute_decl =
  let open Monad.Notation (EM) in
  function
  | CS.Def {name; args; def; tp} ->
    let* _tp, vtp, _tm, vtm = elaborate_typed_term (Ident.to_string name) args tp def in
    let+ _sym = EM.add_global name vtp @@ Some vtm in
    `Continue
  | CS.NormalizeTerm term ->
    EM.veil (Veil.const `Transparent)
    begin
      EM.trap (Elaborator.syn_tm term) |>>
      function
      | Ok (tm, vtp) ->
        let* vtm = EM.lift_ev @@ Sem.eval tm in
        let* tm' = EM.lift_qu @@ Qu.quote_con vtp vtm in
        let+ () = EM.emit term.info pp_message @@ NormalizedTerm {orig = tm; nf = tm'} in
        `Continue
      | Error (Elaborator.NotSynthesizable con) ->
        let+ () = EM.emit ~lvl:`Error con.info pp_message @@ TermNotSynthesizable con.node in
        `Continue
      | Error err -> EM.throw err
    end
  | CS.Print ident ->
    begin
      EM.resolve ident.node |>>
      function
      | `Global sym ->
        let* vtp, con = EM.get_global sym in
        let* tp = EM.lift_qu @@ Qu.quote_tp vtp in
        let* tm =
          match con with
          | None -> EM.ret None
          | Some con ->
            let* tm = EM.lift_qu @@ Qu.quote_con vtp con in
            EM.ret @@ Some tm
        in
        let+ () = EM.emit ident.info pp_message @@ Definition {ident = ident.node; tp; tm} in
        `Continue
      | _ ->
        let+ () = EM.emit ~lvl:`Error ident.info pp_message @@ UnboundIdent ident.node in
        `Continue
    end
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
