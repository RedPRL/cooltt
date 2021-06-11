open Core
open Basis
open CodeUnit
open DriverMessage

module CS = ConcreteSyntax
module S = Syntax
module D = Domain
module Env = RefineEnv
module Err = RefineError
module Sem = Semantics
module Qu = Quote

module RM = RefineMonad
module ST = RefineState
module RMU = Monad.Util (RM)
open Monad.Notation (RM)

type status = (unit, unit) Result.t
type continuation = Continue of (status RM.m -> status RM.m) | Quit
type command = continuation RM.m

(* Refinement Helpers *)

let elaborate_typed_term name (args : CS.cell list) tp tm =
  RM.push_problem name @@
  let* tp = RM.push_problem "tp" @@ Tactic.Tp.run @@ Elaborator.chk_tp_in_tele args tp in
  let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
  let* tm = RM.push_problem "tm" @@ Tactic.Chk.run (Elaborator.chk_tm_in_tele args tm) vtp in
  let+ vtm = RM.lift_ev @@ Sem.eval tm in
  vtp, vtm

let add_global name vtp con : command =
  let+ _ = RM.add_global name vtp con in
  let kont = match vtp with | D.TpPrf phi -> RM.restrict [phi] | _ -> Fun.id in
  Continue kont

let print_ident (ident : Ident.t CS.node) : command =
  RM.resolve ident.node |>>
  function
  | `Global sym ->
    let* vtp, con = RM.get_global sym in
    let* tp = RM.quote_tp vtp in
    let* tm =
      match con with
      | None -> RM.ret None
      | Some con ->
        let* tm = RM.quote_con vtp con in
        RM.ret @@ Some tm
    in
    let+ () =
      RM.emit ident.info pp_message @@
      OutputMessage (Definition {ident = ident.node; tp; tm})
    in
    Continue Fun.id
  | _ ->
    RM.throw @@ Err.RefineError (Err.UnboundVariable ident.node, ident.info)

let protect m =
  RM.trap m |>> function
  | Ok return ->
    RM.ret @@ Ok return
  | Error (Err.RefineError (err, info)) ->
    let+ () = RM.emit ~lvl:`Error info RefineError.pp err in
    Error ()
  | Error exn ->
    let* env = RM.read in
    let+ () = RM.emit ~lvl:`Error (RefineEnv.location env) PpExn.pp exn in
    Error ()

(* Imports *)

let find_project_root () =
  let working_dir = Sys.getcwd () in
  let rec go dir =
    if Sys.file_exists "cooltt-lib" then
      Some dir
    else
      let () = Sys.chdir Filename.parent_dir_name in
      let parent = Sys.getcwd () in
      if parent = dir then
        let () = Log.pp_runtime_message ~loc:None ~lvl:`Warn pp_message @@ WarningMessage MissingProject in
        None
      else
        go parent
  in let project_root = go working_dir in
  let _ = Sys.chdir working_dir in
  project_root

let resolve_source_path project_root imp =
  match project_root with
  | Some root -> Filename.concat root (imp ^ ".cooltt")
  | None -> imp ^ ".cooltt"

(* Create an interface file for a given source file. *)
let rec build_code_unit ~project_root src_path =
  let* _ = process_file ~project_root (`File src_path) in
  RM.get_current_unit

and load_code_unit ~project_root imp =
  let src_path = resolve_source_path project_root imp in
  RM.with_code_unit src_path (fun () -> build_code_unit ~project_root src_path)

and import_code_unit project_root path : command =
  let* unit_loaded = RM.get_import path in
  let* import_unit =
    match unit_loaded with
    | Some import_unit -> RM.ret import_unit
    | None -> load_code_unit ~project_root path in
  let* _ = RM.add_import [] import_unit in
  RM.ret @@ Continue Fun.id

and execute_decl ~project_root : CS.decl -> command =
  function
  | CS.Def {name; args; def = Some def; tp} ->
    let* vtp, vtm = elaborate_typed_term (Ident.to_string name) args tp def in
    add_global name vtp @@ Some vtm
  | CS.Def {name; args; def = None; tp} ->
    let* tp = Tactic.Tp.run @@ Elaborator.chk_tp_in_tele args tp in
    let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
    add_global name vtp None
  | CS.NormalizeTerm term ->
    RM.veil (Veil.const `Transparent) @@
    let* tm, vtp = Tactic.Syn.run @@ Elaborator.syn_tm term in
    let* vtm = RM.lift_ev @@ Sem.eval tm in
    let* tm' = RM.quote_con vtp vtm in
    let+ () = RM.emit term.info pp_message @@ OutputMessage (NormalizedTerm {orig = tm; nf = tm'}) in
    Continue Fun.id
  | CS.Print ident ->
    print_ident ident
  | CS.Import path ->
     import_code_unit project_root path
  | CS.Quit ->
    RM.ret Quit

and execute_signature ~project_root ~status sign =
  match sign with
  | [] -> RM.ret status
  | d :: sign ->
    let* res = protect @@ execute_decl ~project_root d in
    match res with
    | Ok Continue k ->
      k @@ execute_signature ~project_root ~status sign
    | Ok Quit ->
      RM.ret @@ Ok ()
    | Error () ->
      RM.ret @@ Error ()

and process_file ~project_root input =
  match Load.load_file input with
  | Ok sign -> execute_signature ~project_root ~status:(Ok ()) sign
  | Error (Load.ParseError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = ParseError; last_token = err.last_token};
    RM.ret @@ Error ()
  | Error (Load.LexingError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = LexingError; last_token = err.last_token};
    RM.ret @@ Error ()

let load_file input =
  let project_root = find_project_root () in
  RM.run_exn (ST.init "<unit>") Env.init @@ process_file ~project_root input

let execute_command ~project_root =
  function
  | CS.Decl decl -> execute_decl ~project_root decl
  | CS.NoOp -> RM.ret @@ Continue Fun.id
  | CS.EndOfFile -> RM.ret Quit

let rec repl ~project_root (ch : in_channel) lexbuf =
  match Load.load_cmd lexbuf with
  | Error (Load.ParseError {span; last_token}) ->
    let* () = RM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = ParseError; last_token} in
    repl ~project_root ch lexbuf
  | Error (Load.LexingError {span; last_token}) ->
    let* () = RM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = LexingError; last_token} in
    repl ~project_root ch lexbuf
  | Ok cmd ->
    protect @@ execute_command ~project_root cmd |>>
    function
    | Ok (Continue k) ->
      k @@ repl ~project_root ch lexbuf
    | Error _  ->
      repl ~project_root ch lexbuf
    | Ok Quit ->
      close_in ch;
      RM.ret @@ Ok ()

let do_repl () =
  let ch, lexbuf = Load.prepare_repl () in
  let project_root = find_project_root () in
  RM.run_exn (RefineState.init "<repl>") Env.init @@
  repl ~project_root ch lexbuf
