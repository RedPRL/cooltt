module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = ElabEnv
module Err = ElabError
module Sem = Semantics
module Qu = Quote
open Basis


(* TODO: refactoring the error handling *)

type message =
  | LexingError
  | ParseError
  | NormalizedTerm of {orig : S.t; nf : S.t}
  | Definition of {ident : Ident.t; tp : S.tp; tm : S.t option}
  | UnboundIdent of Ident.t

let pp_message fmt =
  function
  | ParseError ->
    Format.pp_print_string fmt "Parse error"
  | LexingError ->
    Format.pp_print_string fmt "Lexing error"
  | NormalizedTerm {orig; nf} ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[Computed normal form of@ @[<hv>%a@] as@,@[<hv> %a@]@]"
      (S.pp env) orig
      (S.pp env) nf
  | Definition {ident; tp; tm = Some tm} ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[<v>%a@ : %a@ = %a@]"
      Ident.pp ident
      (S.pp_atomic_tp env) tp
      (S.pp_atomic env) tm
  | Definition {ident; tp; tm = None} ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[%a : %a@]"
      Ident.pp ident
      (S.pp_atomic_tp env) tp
  | UnboundIdent ident ->
    Format.fprintf fmt
      "@[Unbound identifier %a@]"
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
    Ok `Continue
  | CS.NormalizeTerm term ->
    EM.veil (Veil.const `Transparent)
      begin
        EM.trap (Elaborator.syn_tm term) |>>
        function
        | Ok (tm, vtp) ->
          let* vtm = EM.lift_ev @@ Sem.eval tm in
          let* tm' = EM.quote_con vtp vtm in
          let+ () = EM.emit term.info pp_message @@ NormalizedTerm {orig = tm; nf = tm'} in
          Ok `Continue
        | Error (Err.ElabError (err, info)) ->
          let+ () = EM.emit ~lvl:`Error info ElabError.pp err in
          Error `Continue
        | Error err -> EM.throw err
      end
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
        let+ () = EM.emit ident.info pp_message @@ Definition {ident = ident.node; tp; tm} in
        Ok `Continue
      | _ ->
        let+ () = EM.emit ~lvl:`Error ident.info pp_message @@ UnboundIdent ident.node in
        Ok `Continue
    end
  | CS.Quit ->
    EM.ret @@ Ok `Quit

(* Favonia: I haven't decided to extend the environment to hold past errors. *)
let rec execute_signature ~status sign =
  let open Monad.Notation (EM) in
  match sign with
  | [] -> EM.ret status
  | d :: sign ->
    let* res = execute_decl d in
    let cont, status =
      Result.fold
        ~ok:(fun o -> o, status)
        ~error:(fun e -> e, Error ())
        res
    in
    match cont with
    | `Continue ->
      execute_signature ~status sign
    | `Quit ->
      EM.ret status

let process_sign : CS.signature -> (unit, unit) result =
  fun sign ->
  EM.run_exn ElabState.init Env.init @@
  execute_signature ~status:(Ok ()) sign

let process_file input =
  match Load.load_file input with
  | Ok sign -> process_sign sign
  | Error (Load.ParseError span) ->
    Log.pp_message ~loc:(Some span) ~lvl:`Error pp_message @@ ParseError;
    Error ()
  | Error (Load.LexingError span) ->
    Log.pp_message ~loc:(Some span) ~lvl:`Error pp_message @@ LexingError;
    Error ()

let execute_command =
  let open Monad.Notation (EM) in
  function
  | CS.Decl decl -> execute_decl decl
  | NoOp -> EM.ret @@ Ok `Continue
  | CS.EndOfFile -> EM.ret @@ Ok `Quit

let rec repl (ch : in_channel) lexbuf =
  let open Monad.Notation (EM) in
  match Load.load_cmd lexbuf with
  | Error (Load.ParseError span) ->
    let* () = EM.emit ~lvl:`Error (Some span) pp_message @@ ParseError in
    repl ch lexbuf
  | Error (Load.LexingError span) ->
    let* () = EM.emit ~lvl:`Error (Some span) pp_message @@ LexingError in
    repl ch lexbuf
  | Ok cmd ->
    let* res = execute_command cmd in
    match res with
    | Ok `Continue ->
      repl ch lexbuf
    | Error `Continue ->
      repl ch lexbuf
    | Ok `Quit ->
      close_in ch;
      EM.ret @@ Ok ()
    | Error `Quit ->
      close_in ch;
      EM.ret @@ Error ()

let do_repl () =
  let ch, lexbuf = Load.prepare_repl () in
  EM.run_exn ElabState.init Env.init @@
  repl ch lexbuf
