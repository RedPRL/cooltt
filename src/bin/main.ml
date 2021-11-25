open Server
open Frontend
open Cmdliner

let _ =
  Printexc.record_backtrace false;
  ()

type mode =
  [ `Interactive
  | `Scripting of [`Stdin | `File of string]
  | `Server
  ]

type options =
  { mode : mode;
    as_file : string option;
    width : int;
    debug_mode : bool;
  }

let options mode as_file width debug_mode =
  { mode; as_file; width; debug_mode }

let main {mode; as_file; width; debug_mode; _} =
  Format.set_margin width;
  match
    match mode with
    | `Interactive -> Driver.do_repl {as_file; debug_mode}
    | `Scripting input -> Driver.load_file {as_file; debug_mode;} input
    | `Server -> LanguageServer.run ()
  with
  | Ok () -> `Ok ()
  | Error () -> `Error (false, "encountered one or more errors")

let opt_mode =
  let doc =
    "Set the interaction mode. "^
    "The value $(docv) must be one of "^
    "$(b,scripting) (default), $(b,interactive), or $(b,server)." in
  Arg.(value & opt (some string) None & info ["m"; "mode"] ~doc ~docv:"MODE")

let opt_interactive =
  let doc = "An abbreviation of $(b,--mode interactive)." in
  Arg.(value & flag & info ["i"; "interactive"] ~doc)

let opt_width =
  let default_width = Format.get_margin () in
  let doc = "Set the maximum output width to $(docv) columns." in
  Arg.(value & opt int default_width & info ["w"; "width"] ~doc ~docv:"NUM")

let opt_input_file =
  let doc = "The file to typecheck. When $(docv) is -, read standard input." in
  let parse_dash = Term.(app @@ const @@ Option.map @@ fun str -> if str = "-" then `Stdin else `File str) in
  Arg.(parse_dash & value & pos ~rev:true 0 (some string) None & info [] ~doc ~docv:"FILE")

let opt_as_file =
  let doc = "Pretend the input was located at $(docv) when searching for the project root. \
             This is mainly useful when reading from stdin."
  in
  Arg.(value & opt (some string) None & info ["as-file"] ~doc ~docv:"FILE")

let opt_debug =
  let doc = "Enable debug mode. This will print out a bunch of information pertaining to the internal operations of cooltt."
  in
  Arg.(value & flag & info ["debug"] ~doc)

let myinfo =
  let doc = "elaborate and normalize terms in Cartesian cubical type theory" in
  let err_exit = Term.exit_info ~doc:"on ill-formed types or terms." 1 in
  Term.info "cooltt" ~version:"0.0" ~doc
    ~exits:(err_exit :: Term.default_exits)

let parse_mode =
  function
  | "interactive" -> `Interactive
  | "scripting" -> `Scripting
  | "server" -> `Server
  | s -> `Nonexistent s

let quote s = "`" ^ s ^ "'"

let consolidate_input_options mode interactive input_file : (mode, [`Msg of string]) result  =
  match Option.map parse_mode mode, interactive, input_file with
  | (Some `Scripting | None), false, Some input_file ->
    Ok (`Scripting input_file)
  | (Some `Scripting | None), false, None ->
    Error (`Msg "scripting mode expects an input file")
  | Some `Interactive, _, None | None, true, None ->
    Ok `Interactive
  | Some `Server, false, None ->
    Ok `Server
  | Some `Interactive, _, Some _ | None, true, _ ->
    Error (`Msg "interactive mode expects no input files")
  | Some `Server, _, Some _ ->
    Error (`Msg "server mode expects no input files")
  | Some `Scripting, true, _ ->
    Error (`Msg "inconsistent mode assignment")
  | Some `Server, true, _ ->
    Error (`Msg "inconsistent mode assignment")
  | Some (`Nonexistent s), _, _ ->
    Error (`Msg ("no mode named " ^ quote s))

let () =
  let opts_input = Term.(term_result ~usage:true (const consolidate_input_options $ opt_mode $ opt_interactive $ opt_input_file))  in
  let options : options Term.t = Term.(const options $ opts_input $ opt_as_file $ opt_width $ opt_debug) in
  let t = Term.ret @@ Term.(const main $ options) in
  Term.exit @@ Term.eval ~catch:true ~err:Format.std_formatter (t, myinfo)
