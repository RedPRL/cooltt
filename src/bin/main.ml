open Core
open Cmdliner

let _ =
  Printexc.record_backtrace true;
  ()

type options = {mode: [`Interactive | `Scripting of [`Stdin | `File of string]]; width: int}

let main {mode; width} =
  Format.set_margin width;
  match
    match mode with
    | `Interactive -> Driver.do_repl ()
    | `Scripting input -> Driver.process_file input
  with
  | Ok () -> `Ok ()
  | Error () -> `Error (false, "there are errors in the script")

let opt_mode =
  let doc =
    "Mode. Currently supported modes include $(b,scripting) (default) and $(b,interactive). "^
    "A prefix that is distinct enough is sufficient. "^
    "For example, $(b,--mode int) means $(b,--mode interactive)." in
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

let myinfo =
  let doc = "elaborate and normalize terms in Cartesian cubical type theory" in
  let err_exit = Term.exit_info ~doc:"on ill-formed types or terms." 1 in
  Term.info "cooltt" ~version:"0.0" ~doc
    ~exits:(err_exit :: Term.default_exits)

let is_prefix substr str =
  let sublen = String.length substr in
  try
    String.equal substr @@ String.sub str 0 sublen
  with Invalid_argument _ -> false

let parse_mode s =
  match is_prefix s "interactive", is_prefix s "scripting" with
  | true, true -> `Ambiguous s
  | false, false -> `Nonexistent s
  | true, false -> `Interactive
  | false, true -> `Scripting

let quote s = "`" ^ s ^ "'"

let consolidate_options mode interactive width input_file : options Term.ret =
  match Option.map parse_mode mode, interactive, width, input_file with
  | (Some `Scripting | None), false, width, Some input_file ->
    `Ok {mode = `Scripting input_file; width}
  | (Some `Scripting | None), false, _, None ->
    `Error (true, "The scripting mode needs an input file")
  | Some `Interactive, _, width, None | None, true, width, None ->
    `Ok {mode = `Interactive; width}
  | Some `Interactive, _, _, Some _ | None, true, _, _ ->
    `Error (true, "No input file allowed in the interactive mode")
  | Some `Scripting, true, _, _ ->
    `Error (true, "Inconsistent mode assignment")
  | Some (`Ambiguous s), _, _, _ ->
    `Error (true, "The mode " ^ quote s ^ " is ambiguous")
  | Some (`Nonexistent s), _, _, _ ->
    `Error (true, "No mode with the prefix " ^ quote s)

let () =
  let options : options Term.t = Term.(ret (const consolidate_options $ opt_mode $ opt_interactive $ opt_width $ opt_input_file)) in
  let t = Term.ret @@ Term.(const main $ options) in
  Term.exit @@ Term.eval ~catch:true ~err:Format.std_formatter (t, myinfo)
