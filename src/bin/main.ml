open Frontend
open Cmdliner

let _ =
  Printexc.record_backtrace false;
  ()

type options =
  { mode : [`Interactive | `Scripting of [`Stdin | `File of string]];
    as_file : string option;
    width : int;
    debug_mode : bool;
    server_port : int option }

let main {mode; as_file; width; debug_mode; server_port} =
  Format.set_margin width;
  match
    match mode with
    | `Interactive -> Driver.do_repl {as_file; debug_mode; server_port}
    | `Scripting input -> Driver.load_file {as_file; debug_mode; server_port} input
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
  Arg.(value & opt (some int) None & info ["server"] ~doc ~docv:"PORT")

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

let consolidate_options mode interactive width input_file as_file debug_mode server_port : options Term.ret =
  match Option.map parse_mode mode, interactive, width, input_file with
  | (Some `Scripting | None), false, width, Some input_file ->
    `Ok {mode = `Scripting input_file; as_file; width; debug_mode; server_port}
  | (Some `Scripting | None), false, _, None ->
    `Error (true, "scripting mode expects an input file")
  | Some `Interactive, _, width, None | None, true, width, None ->
    `Ok {mode = `Interactive; as_file; width; debug_mode; server_port}
  | Some `Interactive, _, _, Some _ | None, true, _, _ ->
    `Error (true, "interactive mode expects no input files")
  | Some `Scripting, true, _, _ ->
    `Error (true, "inconsistent mode assignment")
  | Some (`Nonexistent s), _, _, _ ->
    `Error (true, "no mode named " ^ quote s)

let () =
  let options : options Term.t =
    Term.(ret (const consolidate_options $ opt_mode $ opt_interactive $ opt_width $ opt_input_file $ opt_as_file $ opt_debug $ opt_server))
  in
  let t = Term.ret @@ Term.(const main $ options) in
  exit (Cmd.eval ~catch:true ~err:Format.std_formatter @@ Cmd.v myinfo t)
