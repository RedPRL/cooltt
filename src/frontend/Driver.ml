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
module TB = TermBuilder

module RM = RefineMonad
module R = Refiner
module ST = RefineState
module RMU = Monad.Util (RM)
open Monad.Notation (RM)

type status = (unit, unit) Result.t
type continuation = Continue | Quit
type command = continuation RM.m

(* Refinement Helpers *)

let elaborate_typed_term _name (args : CS.cell list) (tp : CS.con) (tm : CS.con) =
  let* tp = Tactic.Tp.run @@ Elaborator.chk_tp_in_tele args tp in
  let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
  let* tm = Tactic.Chk.run (Elaborator.chk_tm_in_tele args tm) vtp in
  let+ vtm = RM.lift_ev @@ Sem.eval tm in
  vtp, vtm

let print_ident (ident : Ident.t CS.node) : command =
  RM.resolve ident.node |>>
  function
  | `Global sym ->
    let* vtp = RM.get_global sym in
    let* tp = RM.quote_tp vtp in
    let+ () =
      RM.emit ident.info pp_message @@
      OutputMessage (Definition {ident = ident.node; tp})
    in
    Continue
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
  RM.with_unit lib (CodeUnitID.file src) @@ build_code_unit src

and import_unit ~shadowing path modifier : command =
  let* lib = RM.get_lib in
  match resolve_source_path lib path with
  | Error () -> RM.ret Quit
  | Ok (lib, _, src) ->
    let* () =
      RM.loading_status (CodeUnitID.file src) |>>
      function
      | `Loaded -> RM.ret ()
      | `Unloaded -> load_code_unit lib src
      | `Loading -> RM.refine_err @@ CyclicImport (CodeUnitID.file src)
    in
    let+ () = RM.import ~shadowing modifier (CodeUnitID.file src) in
    Continue

and execute_decl (decl : CS.decl) : command =
  RM.update_span (CS.get_info decl) @@
  match decl.node with
  | CS.Def {abstract; shadowing; name; args; def; tp; requiring; unfolding} ->
    Debug.print "Defining %a@." Ident.pp name;

    (* Unleash the unfolding dimension for the term component *)
    let* unf_dim_sym =
      match abstract, requiring, unfolding with
      | false, [], [] -> RM.ret None
      | _, _,_ ->
        let+ var = RM.add_global ~unfolder:None ~guarded:false ~shadowing:false (Ident.unfolder name) D.TpDim in
        Some var
    in

    let* unf_dim =
      match unf_dim_sym with
      | None -> RM.ret D.Dim1
      | Some var -> RM.eval @@ S.Global var
    in

    let* requirement_syms = RM.resolve_unfolder_syms requiring in
    let* unfolding_syms = RM.resolve_unfolder_syms unfolding in
    let* requirement_dims =  requirement_syms |> RMU.map @@ fun sym -> RM.eval @@ S.Global sym in
    let* unfolding_dims =  unfolding_syms |> RMU.map @@ fun sym -> RM.eval @@ S.Global sym in

    let* _ =
      requirement_dims @ unfolding_dims |> RMU.iter @@ fun dim ->
      let* cof = RM.lift_cmp @@ Sem.con_to_cof @@ D.CofBuilder.le unf_dim dim in
      RMU.ignore @@
      RM.add_global ~unfolder:None ~guarded:false ~shadowing:false Ident.anon @@ D.TpPrf cof
    in

    let* unf_cof = RM.lift_cmp @@ Sem.con_to_cof @@ D.CofBuilder.eq unf_dim D.Dim1 in

    let* requirement_cof =
      RM.lift_cmp @@
      Sem.con_to_cof @@
      D.CofBuilder.meet @@
      List.map (D.CofBuilder.eq D.Dim1) requirement_dims
    in

    let* ttp_body =
      Tactic.abstract (D.TpPrf requirement_cof) @@ fun _ ->
      Tactic.Tp.run @@ Elaborator.chk_tp_in_tele args tp
    in

    let* treq_cof = RM.quote_cof requirement_cof in

    let* abstract_vtp =
      let* vsub =
        RM.abstract Ident.anon (D.TpPrf requirement_cof) @@ fun _ ->
        let* tunf_cof = RM.quote_cof unf_cof in
        let* vtp_body = RM.eval_tp ttp_body in
        let* bdy =
          Tactic.abstract (D.TpPrf unf_cof) @@ fun _ ->
          let* tm = Tactic.Chk.run (Elaborator.chk_tm_in_tele args def) vtp_body in
          RM.ret @@ S.Sub (ttp_body, tunf_cof, tm)
        in
        RM.ret @@
        S.Pi (S.TpPrf treq_cof, Ident.anon, bdy)
      in
      RM.eval_tp vsub
    in

    let+ _ =
      RM.add_global
        ~unfolder:unf_dim_sym
        ~guarded:true
        ~shadowing
        name
        abstract_vtp
    in
    Continue

  | CS.Axiom {shadowing; name; args; tp; requiring} ->
    Debug.print "Defining Axiom %a@." Ident.pp name;

    let* requirement_syms = RM.resolve_unfolder_syms requiring in

    let* requirement_dims =
      requirement_syms |> RMU.map @@ fun sym ->
      RM.eval @@ S.Global sym
    in

    let* requirement_cof =
      RM.lift_cmp @@
      Sem.con_to_cof @@
      D.CofBuilder.meet @@
      List.map (D.CofBuilder.eq D.Dim1) requirement_dims
    in

    let* tp, guarded =
      match requiring with
      | [] ->
        let+ tp = Tactic.Tp.run_virtual @@ Elaborator.chk_tp_in_tele args tp in
        tp, false
      | _ ->
        let+ treqcof = RM.quote_cof requirement_cof
        and+ bdy =
          RM.abstract Ident.anon (D.TpPrf requirement_cof) @@ fun _ ->
          Tactic.Tp.run @@ Elaborator.chk_tp_in_tele args tp
        in
        S.Pi (S.TpPrf treqcof, Ident.anon, bdy), true
    in

    let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
    let* _ = RM.add_global ~unfolder:None ~guarded ~shadowing name vtp in
    RM.ret Continue

  | CS.NormalizeTerm term ->
    RM.veil `Transparent @@
    let* tm, vtp = Tactic.Syn.run @@ Elaborator.syn_tm term in
    let* vtm = RM.lift_ev @@ Sem.eval tm in
    let* tm' = RM.quote_con vtp vtm in
    let* () = RM.emit term.info pp_message @@ OutputMessage (NormalizedTerm {orig = tm; nf = tm'}) in
    RM.ret Continue

  | CS.Fail decl ->
    let wrap_pp_exn fmt exn =
      Format.fprintf fmt
        "Failure encountered, as expected:@, @[<v>%a@]@."
        PpExn.pp exn
    in
    begin
      RM.trap @@ execute_decl decl |>>
      function
      | Ok _ ->
        RM.throw @@ ElabError.ElabError (ElabError.ExpectedFailure decl, decl.info)
      | Error exn ->
        let+ () = RM.emit ~lvl:`Info decl.info wrap_pp_exn exn in
        Continue
    end

  | CS.Print ident ->
    print_ident ident
  | CS.Import {shadowing; unitpath; modifier} ->
    RM.update_span (Option.fold ~none:None ~some:CS.get_info modifier) @@
    let* modifier = Option.fold ~none:(RM.ret Yuujinchou.Pattern.any) ~some:Elaborator.modifier modifier in
    import_unit ~shadowing unitpath modifier
  | CS.View {shadowing; modifier} ->
    RM.update_span (CS.get_info modifier) @@
    let* modifier = Elaborator.modifier modifier in
    let* () = RM.view ~shadowing modifier in
    RM.ret Continue
  | CS.Export {shadowing; modifier} ->
    RM.update_span (CS.get_info modifier) @@
    let* modifier = Elaborator.modifier modifier in
    let* () = RM.export ~shadowing modifier in
    RM.ret Continue
  | CS.Repack {shadowing; modifier} ->
    RM.update_span (CS.get_info modifier) @@
    let* modifier = Elaborator.modifier modifier in
    let* () = RM.repack ~shadowing modifier in
    RM.ret Continue
  | CS.Section {shadowing; prefix; decls; modifier} ->
    RM.with_section ~shadowing ~prefix begin
      execute_signature decls |>>
      function
      | Ok () ->
        RM.update_span (Option.fold ~none:None ~some:CS.get_info modifier) @@
        let* modifier = Option.fold ~none:(RM.ret @@ Yuujinchou.Pattern.seq []) ~some:Elaborator.modifier modifier in
        let* () = RM.repack ~shadowing modifier in
        RM.ret Continue
      | Error () -> RM.refine_err ErrorsInSection
    end
  | CS.Quit ->
    RM.ret Quit

and execute_signature =
  function
  | [] -> RM.ret @@ Ok ()
  | d :: sign ->
    let* res = protect @@ execute_decl d in
    match res with
    | Ok Continue ->
      execute_signature sign
    | Ok Quit ->
      RM.ret @@ Ok ()
    | Error () ->
      RM.ret @@ Error ()

and process_file input =
  match Load.load_file input with
  | Ok sign -> execute_signature sign
  | Error (Load.ParseError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = ParseError; last_token = err.last_token};
    RM.ret @@ Error ()
  | Error (Load.LexingError err) ->
    Log.pp_error_message ~loc:(Some err.span) ~lvl:`Error pp_message @@ ErrorMessage {error = LexingError; last_token = err.last_token};
    RM.ret @@ Error ()

let load_file ~as_file ~debug_mode input : status =
  match load_current_library ~as_file input with
  | Error () -> Error ()
  | Ok lib ->
    Debug.debug_mode debug_mode;
    let unit_id = assign_unit_id ~as_file input in
    RM.run_exn (ST.init lib) Env.init @@
    RM.with_unit lib unit_id @@
    process_file input

let execute_command (cmd : CS.repl_command) =
  RM.update_span cmd.info @@
  match cmd.node with
  | CS.Decl decl -> execute_decl decl
  | CS.NoOp -> RM.ret Continue
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
    | Ok Continue ->
      repl lib ch lexbuf
    | Error _  ->
      repl lib ch lexbuf
    | Ok Quit ->
      close_in ch;
      RM.ret @@ Ok ()

let do_repl ~as_file ~debug_mode : status =
  match load_current_library ~as_file `Stdin with
  | Error () -> Error ()
  | Ok lib ->
    Debug.debug_mode debug_mode;
    let unit_id = assign_unit_id ~as_file `Stdin in
    let ch, lexbuf = Load.prepare_repl () in
    RM.run_exn (ST.init lib) Env.init @@
    RM.with_unit lib unit_id @@
    repl lib ch lexbuf
