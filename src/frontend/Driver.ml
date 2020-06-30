open Core
open Basis
open DriverMessage

module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = RefineEnv
module Err = RefineError
module Sem = Semantics
module Qu = Quote


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
    Tactic.Chk.run (Elaborator.chk_tm_in_tele args tm) vtp
  in
  let+ vtm = EM.lift_ev @@ Sem.eval tm in
  tp, vtp, tm, vtm

let execute_decl : CS.decl -> [`Continue | `Quit] EM.m =
  let open Monad.Notation (EM) in
  function
  | CS.Def {name; args; def; tp} ->
    let* _tp, vtp, _tm, vtm = elaborate_typed_term (Ident.to_string name) args tp def in
    let+ _sym = EM.add_global name vtp @@ Some vtm in
    `Continue
  | CS.NormalizeTerm term ->
    EM.veil (Veil.const `Transparent) @@
    let* tm, vtp = Tactic.Syn.run @@ Elaborator.syn_tm term in
    let* vtm = EM.lift_ev @@ Sem.eval tm in
    let* tm' = EM.quote_con vtp vtm in
    let+ () = EM.emit term.info pp_message @@ (OutputMessage (NormalizedTerm {orig = tm; nf = tm'})) in
    `Continue
  | CS.Print ident ->
    begin
      EM.resolve ident.node |>>
      function
      | `Global sym ->
        let* vtp, con = EM.get_global sym in
        let* tp = EM.quote_tp vtp in
        let* tm =
          match con with
          | None -> EM.ret None
          | Some con ->
            let* tm = EM.quote_con vtp con in
            EM.ret @@ Some tm
        in
        let+ () = EM.emit ident.info pp_message @@ (OutputMessage (Definition {ident = ident.node; tp; tm})) in
        `Continue
      | _ ->
        EM.throw @@ Err.RefineError (Err.UnboundVariable ident.node, ident.info)
    end
  | CS.Quit ->
    EM.ret `Quit


let protect m =
  let open Monad.Notation (EM) in
  EM.trap m |>> function
  | Ok return ->
    EM.ret @@ Ok return
  | Error (Err.RefineError (err, info)) ->
    let+ () = EM.emit ~lvl:`Error info RefineError.pp err in
    Error ()
  | Error exn ->
    let* env = EM.read in
    let+ () = EM.emit ~lvl:`Error (RefineEnv.location env) PpExn.pp exn in
    Error ()

let rec execute_signature ~status sign =
  let open Monad.Notation (EM) in
  match sign with
  | [] -> EM.ret status
  | d :: sign ->
    let* res = protect @@ execute_decl d in
    match res with
    | Ok `Continue ->
      execute_signature ~status sign
    | Ok `Quit ->
      EM.ret @@ Ok ()
    | Error () ->
      EM.ret @@ Error ()

let process_sign : CS.signature -> (unit, unit) result =
  fun sign ->
  EM.run_exn RefineState.init Env.init @@
  execute_signature ~status:(Ok ()) sign

let process_file input =
  match Load.load_file input with
  | Ok sign -> process_sign sign
  | Error (Load.ParseError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = ParseError; last_token = err.last_token};
    Error ()
  | Error (Load.LexingError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = LexingError; last_token = err.last_token};
    Error ()

let execute_command =
  let open Monad.Notation (EM) in
  function
  | CS.Decl decl -> execute_decl decl
  | CS.NoOp -> EM.ret `Continue
  | CS.EndOfFile -> EM.ret `Quit

let rec repl (ch : in_channel) lexbuf =
  let open Monad.Notation (EM) in
  match Load.load_cmd lexbuf with
  | Error (Load.ParseError {span; last_token}) ->
    let* () = EM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = ParseError; last_token} in
    repl ch lexbuf
  | Error (Load.LexingError {span; last_token}) ->
    let* () = EM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = LexingError; last_token} in
    repl ch lexbuf
  | Ok cmd ->
    protect @@ execute_command cmd |>>
    function
    | Ok `Continue ->
      repl ch lexbuf
    | Error _  ->
      repl ch lexbuf
    | Ok `Quit ->
      close_in ch;
      EM.ret @@ Ok ()

let do_repl () =
  let ch, lexbuf = Load.prepare_repl () in
  EM.run_exn RefineState.init Env.init @@
  repl ch lexbuf