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

module RM = RefineMonad
module ST = RefineState
open Monad.Notation (RM)

type status = (unit, unit) Result.t
type continuation = Continue of (status RM.m -> status RM.m) | Quit
type command = continuation RM.m 

(* Refinement Helpers *)

let elaborate_typed_term name (args : CS.cell list) tp tm =
  RM.push_problem name @@
  let* tp = RM.push_problem "tp" @@ Tactic.Tp.run_virtual @@ Elaborator.chk_tp_in_tele args tp in
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

(* Interfaces and Imports *)

type iface = { contents : ST.t;
               hash: Digest.t }

let resolve_import_path imp =
  imp ^ ".cooltt"

let resolve_iface_path src_path =
  Filename.remove_extension src_path ^ ".cooltti"

(* Try to load an interface file, failing if the file does not exist or is out of date. *)
let load_iface_opt src_path =
  let iface_path = resolve_iface_path src_path in
  if Sys.file_exists iface_path then
    let chan = open_in_bin iface_path in
    let iface = Marshal.from_channel chan in
    let _ = close_in chan in
    if iface.hash == Digest.file src_path then
      Some iface
    else
      None
  else
    None

(* Create an interface file for a given source file. *)
let rec build_iface src_path =
  let iface_path = resolve_iface_path src_path in
  let digest = Digest.file src_path in
  match process_import (`File src_path) with
  | Ok st ->
     let iface = { contents = st; hash = digest } in
     let chan = open_out_bin iface_path in
     let _ = Marshal.to_channel chan iface [Marshal.No_sharing] in
     let _ = close_out chan in
     Ok iface
  | Error () -> Error ()

and load_iface imp =
  let src_path = resolve_import_path imp in
  match load_iface_opt src_path with
  | Some iface -> iface
  | None -> build_iface src_path

and import_module path : command =
  match load_iface path with
  | Ok iface ->
     let* () = RM.modify (ST.add_import [] iface.contents) in
     RM.ret @@ Continue Fun.id
  | Error () -> RM.ret Quit

and execute_decl : CS.decl -> command =
  function
  | CS.Def {name; args; def = Some def; tp} ->
    let* vtp, vtm = elaborate_typed_term (Ident.to_string name) args tp def in
    add_global name vtp @@ Some vtm
  | CS.Def {name; args; def = None; tp} ->
    let* tp = Tactic.Tp.run_virtual @@ Elaborator.chk_tp_in_tele args tp in
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
     import_module path
  | CS.Quit ->
    RM.ret Quit

and execute_signature ~status sign =
  match sign with
  | [] -> RM.ret status
  | d :: sign ->
    let* res = protect @@ execute_decl d in
    match res with
    | Ok Continue k ->
      k @@ execute_signature ~status sign
    | Ok Quit ->
      RM.ret @@ Ok ()
    | Error () ->
      RM.ret @@ Error ()

and process_sign sign =
  RM.run_globals_exn RefineState.init Env.init @@
  execute_signature ~status:(Ok ()) sign

(* Process a file, returning the resulting refiner state after execution. *)
and process_import input =
  match Load.load_file input with
  | Ok sign ->
     let (res, st) = process_sign sign
     in Result.map (Fun.const st) res
  | Error (Load.ParseError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = ParseError; last_token = err.last_token};
    Error ()
  | Error (Load.LexingError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = LexingError; last_token = err.last_token};
    Error ()

let process_file input =
  Result.map ignore @@ process_import input

let execute_command =
  function
  | CS.Decl decl -> execute_decl decl
  | CS.NoOp -> RM.ret @@ Continue Fun.id
  | CS.EndOfFile -> RM.ret Quit

let rec repl (ch : in_channel) lexbuf =
  match Load.load_cmd lexbuf with
  | Error (Load.ParseError {span; last_token}) ->
    let* () = RM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = ParseError; last_token} in
    repl ch lexbuf
  | Error (Load.LexingError {span; last_token}) ->
    let* () = RM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = LexingError; last_token} in
    repl ch lexbuf
  | Ok cmd ->
    protect @@ execute_command cmd |>>
    function
    | Ok (Continue k) ->
      k @@ repl ch lexbuf
    | Error _  ->
      repl ch lexbuf
    | Ok Quit ->
      close_in ch;
      RM.ret @@ Ok ()

let do_repl () =
  let ch, lexbuf = Load.prepare_repl () in
  RM.run_exn RefineState.init Env.init @@
  repl ch lexbuf
