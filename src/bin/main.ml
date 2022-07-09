open Frontend
open Cmdliner

let _ =
  Printexc.record_backtrace false;
  ()

type mode =
  [ `Interactive
  | `Scripting of [`Stdin | `File of string]
  ]

type options =
  { mode : mode;
    as_file : string option;
    width : int;
    debug_mode : bool;
    server_info : (string * int) option;
  }

let options mode as_file width debug_mode server_info =
  { mode; as_file; width; debug_mode; server_info }

let main {mode; as_file; width; debug_mode; server_info} =
  Format.set_margin width;
  match
    match mode with
    | `Interactive -> Driver.do_repl {as_file; debug_mode; server_info}
    | `Scripting input -> Driver.load_file {as_file; debug_mode; server_info} input
  with
  | Ok () -> `Ok ()
  | Error () -> `Error (false, "encountered one or more errors")

let opt_mode =
  let doc =
    "Set the interaction mode. "^
    "The value $(docv) must be one of "^
    "$(b,scripting) (default) or $(b,interactive)." in
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

let opt_server =
  let doc = "Enable the cooltt hole server."
  in
  Arg.(value & flag & info ["server"] ~doc)

let opt_server_hostname =
  let doc = "The cooltt hole server hostname. If --server is not enabled, this does nothing."
  in
  Arg.(value & opt string "localhost" & info ["server-hostname"] ~doc ~docv:"HOSTNAME")

let opt_server_port =
  let doc = "The cooltt hole server port. If --server is not enabled, this does nothing."
  in
  Arg.(value & opt int 3001 & info ["server-port"] ~doc ~docv:"PORT")

let myinfo =
  let doc = "elaborate and normalize terms in Cartesian cubical type theory" in
  let err_exit = Cmd.Exit.info ~doc:"on ill-formed types or terms." 1 in
  Cmd.info "cooltt" ~version:"0.0" ~doc
    ~exits:(err_exit :: Cmd.Exit.defaults)

let parse_mode =
  function
  | "interactive" -> `Interactive
  | "scripting" -> `Scripting
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
  | Some `Interactive, _, Some _ | None, true, _ ->
    Error (`Msg "interactive mode expects no input files")
  | Some `Scripting, true, _ ->
    Error (`Msg "inconsistent mode assignment")
  | Some (`Nonexistent s), _, _ ->
    Error (`Msg ("no mode named " ^ quote s))

let consolidate_server_options server_enabled server_host server_port =
  if server_enabled
  then Some (server_host, server_port)
  else None

let () =
  let opts_input = Term.(term_result ~usage:true (const consolidate_input_options $ opt_mode $ opt_interactive $ opt_input_file))  in
  let opts_server = Term.(const consolidate_server_options $ opt_server $ opt_server_hostname $ opt_server_port) in
  let options : options Term.t = Term.(const options $ opts_input $ opt_as_file $ opt_width $ opt_debug $ opts_server) in
  let t = Term.ret @@ Term.(const main $ options) in
  exit (Cmd.eval ~catch:true ~err:Format.std_formatter @@ Cmd.v myinfo t)
