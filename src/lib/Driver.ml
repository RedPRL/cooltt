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
  | Definition of {ident : Ident.t; decl : Decl.t}
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
  | Definition {ident; decl} ->
    Decl.pp ident fmt decl
  | UnboundIdent ident ->
    Format.fprintf fmt
      "@[Unbound identifier %a@]"
      Ident.pp ident

module EM = ElabBasics

let elaborate_def cells def tp =
  let open Monad.Notation (EM) in
  let rec go cells =
    match cells with
    | [] ->
      let* tp = Tactic.Tp.run @@ Elaborator.chk_tp tp in
      let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
      let* tm = Tactic.Chk.run (Elaborator.chk_tm def) vtp in
      EM.ret @@ Decl.Return (tp, tm)
    | CS.Cell cell :: cells ->
      let* tp = Tactic.Tp.run_virtual @@ Elaborator.chk_tp cell.tp in
      let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
      Tactic.abstract ~ident:cell.name vtp @@ fun _ ->
      let* decl = go cells in
      EM.ret @@ Decl.Abs (tp, cell.name, decl)
  in
  go cells

let execute_decl : CS.decl -> [`Continue | `Quit] EM.m =
  let open Monad.Notation (EM) in
  function
  | CS.Def {name; args; def; tp} ->
    let* def = elaborate_def args def tp in
    let+ _sym = EM.add_global name def in
    `Continue
  | CS.NormalizeTerm term ->
    EM.veil (Veil.const `Transparent) @@
    let* tm, vtp = Tactic.Syn.run @@ Elaborator.syn_tm term in
    let* vtm = EM.lift_ev @@ Sem.eval tm in
    let* tm' = EM.quote_con vtp vtm in
    let+ () = EM.emit term.info pp_message @@ NormalizedTerm {orig = tm; nf = tm'} in
    `Continue
  | CS.Print ident ->
    begin
      EM.resolve ident.node |>>
      function
      | `Global sym ->
        let* decl = EM.get_global sym in
        let+ () = EM.emit ident.info pp_message @@ Definition {ident = ident.node; decl} in
        `Continue
      | _ ->
        EM.throw @@ Err.ElabError (Err.UnboundVariable ident.node, ident.info)
    end
  | CS.Quit ->
    EM.ret `Quit


let protect m =
  let open Monad.Notation (EM) in
  EM.trap m |>> function
  | Ok return ->
    EM.ret @@ Ok return
  | Error (Err.ElabError (err, info)) ->
    let+ () = EM.emit ~lvl:`Error info ElabError.pp err in
    Error ()
  | Error exn ->
    let* env = EM.read in
    let+ () = EM.emit ~lvl:`Error (ElabEnv.location env) PpExn.pp exn in
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
  EM.run_exn ElabState.init Env.init @@
  execute_signature ~status:(Ok ()) sign

let process_file input =
  match Load.load_file input with
  | Ok sign -> process_sign sign
  | Error (Load.ParseError span) ->
    Log.pp_message ~loc:(Some span) ~lvl:`Error pp_message ParseError;
    Error ()
  | Error (Load.LexingError span) ->
    Log.pp_message ~loc:(Some span) ~lvl:`Error pp_message LexingError;
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
  | Error (Load.ParseError span) ->
    let* () = EM.emit ~lvl:`Error (Some span) pp_message ParseError in
    repl ch lexbuf
  | Error (Load.LexingError span) ->
    let* () = EM.emit ~lvl:`Error (Some span) pp_message LexingError in
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
  EM.run_exn ElabState.init Env.init @@
  repl ch lexbuf
