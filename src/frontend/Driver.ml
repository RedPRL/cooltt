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

let print_fail (name : Ident.t) (info : CS.info) (res : (D.tp * D.con, exn) result) : command =
  match res with
  | Ok (vtp, vtm) ->
    let* tm = RM.quote_con vtp vtm in
    let* tp = RM.quote_tp vtp in
    let* env = RM.read in
    let penv = Env.pp_env env in
    let+ () = RM.emit ~lvl:`Error info (fun fmt () ->
        Format.fprintf fmt "fail %a:@.  Expected (%a : %a) to fail but it succeded."
          Ident.pp name
          (Syntax.pp penv) tm
          (Syntax.pp_tp penv) tp) ()
    in
    Continue Fun.id
  | Error (Err.RefineError (err, info)) ->
    let+ () = RM.emit ~lvl:`Info info (fun fmt () ->
        Format.fprintf fmt "fail %a:@.  %a"
          Ident.pp name
          RefineError.pp err) () in
    Continue Fun.id
  | Error exn ->
    let+ () = RM.emit ~lvl:`Error info PpExn.pp exn in
    Continue Fun.id

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

let library_manager =
  match Bantorra.Manager.init ~anchor:"cooltt-lib" ~routers:[] with
  | Ok ans -> ans
  | Error (`InvalidRouter msg) -> failwith msg (* this should not happen! *)

let load_current_library ~as_file input =
  match
    match as_file with
    | Some fname ->
      Bantorra.Manager.load_library_from_unit library_manager fname ~suffix:".cooltt"
    | None ->
      match input with
      | `File fname ->
        Bantorra.Manager.load_library_from_unit library_manager fname ~suffix:".cooltt"
      | `Stdin ->
        Bantorra.Manager.load_library_from_cwd library_manager
  with
  | Ok (lib, _) -> Ok lib
  | Error (`InvalidLibrary msg) ->
    Log.pp_error_message ~loc:None ~lvl:`Error pp_message @@
    ErrorMessage {error = InvalidLibrary msg; last_token = None};
    Error ()

let assign_unit_id ~as_file input =
  match as_file with
  | Some fname -> CodeUnitID.file fname
  | None ->
    match input with
    | `File fname -> CodeUnitID.file fname
    | `Stdin -> CodeUnitID.top_level

let resolve_source_path lib unitpath =
  match Bantorra.Manager.resolve library_manager lib unitpath ~suffix:".cooltt" with
  | Ok ans -> Ok ans
  | Error (`InvalidLibrary msg) ->
    Log.pp_error_message ~loc:None ~lvl:`Error pp_message @@
    ErrorMessage {error = InvalidLibrary msg; last_token = None};
    Error ()
  | Error (`UnitNotFound msg) ->
    Log.pp_error_message ~loc:None ~lvl:`Error pp_message @@
    ErrorMessage {error = UnitNotFound msg; last_token = None};
    Error ()

(* Create an interface file for a given source file. *)
let rec build_code_unit src_path =
  RMU.ignore @@ process_file (`File src_path)

and load_code_unit lib src =
  RM.with_code_unit lib (CodeUnitID.file src) @@ build_code_unit src

and import_code_unit path modifier : command =
  let* lib = RM.get_current_lib in
  match resolve_source_path lib path with
  | Error () -> RM.ret Quit
  | Ok (lib, _, src) ->
    let* unit_loaded = RM.is_imported (CodeUnitID.file src) in
    let* _ = RMU.guard (not unit_loaded)  (fun () -> load_code_unit lib src) in
    let+ _ = RM.add_import modifier (CodeUnitID.file src) in
    Continue Fun.id

and execute_decl : CS.decl -> command =
  function
  | CS.Def {name; args; def = Some def; tp} ->
    Debug.print "Defining %a@." Ident.pp name;
    let* vtp, vtm = elaborate_typed_term (Ident.to_string name) args tp def in
    add_global name vtp @@ Some vtm
  | CS.Def {name; args; def = None; tp} ->
    Debug.print "Defining Axiom %a@." Ident.pp name;
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
  | CS.Fail {name; args; def; tp; info} ->
    let* res = RM.trap @@ elaborate_typed_term (Ident.to_string name) args tp def in
    print_fail name info res
  | CS.Print ident ->
    print_ident ident
  | CS.Import (path, modifier) ->
    let* modifier = Elaborator.modifier modifier in
    import_code_unit path modifier
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

and process_file input =
  match Load.load_file input with
  | Ok sign -> execute_signature ~status:(Ok ()) sign
  | Error (Load.ParseError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = ParseError; last_token = err.last_token};
    RM.ret @@ Error ()
  | Error (Load.LexingError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = LexingError; last_token = err.last_token};
    RM.ret @@ Error ()

let load_file ~as_file ~debug_mode input =
  match load_current_library ~as_file input with
  | Error () -> Error ()
  | Ok lib ->
    Debug.debug_mode debug_mode;
    let unit_id = assign_unit_id ~as_file input in
    RM.run_exn ST.init (Env.init lib) @@
    RM.with_code_unit lib unit_id @@
    process_file input

let execute_command =
  function
  | CS.Decl decl -> execute_decl decl
  | CS.NoOp -> RM.ret @@ Continue Fun.id
  | CS.EndOfFile -> RM.ret Quit

let rec repl lib (ch : in_channel) lexbuf =
  match Load.load_cmd lexbuf with
  | Error (Load.ParseError {span; last_token}) ->
    let* () = RM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = ParseError; last_token} in
    repl lib ch lexbuf
  | Error (Load.LexingError {span; last_token}) ->
    let* () = RM.emit ~lvl:`Error (Some span) pp_message @@ ErrorMessage {error = LexingError; last_token} in
    repl lib ch lexbuf
  | Ok cmd ->
    protect @@ execute_command cmd |>>
    function
    | Ok (Continue k) ->
      k @@ repl lib ch lexbuf
    | Error _  ->
      repl lib ch lexbuf
    | Ok Quit ->
      close_in ch;
      RM.ret @@ Ok ()

let do_repl ~as_file ~debug_mode =
  match load_current_library ~as_file `Stdin with
  | Error () -> Error ()
  | Ok lib ->
    Debug.debug_mode debug_mode;
    let unit_id = assign_unit_id ~as_file `Stdin in
    let ch, lexbuf = Load.prepare_repl () in
    RM.run_exn RefineState.init (Env.init lib) @@
    RM.with_code_unit lib unit_id @@
    repl lib ch lexbuf
