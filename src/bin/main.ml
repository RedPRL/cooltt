open Core
open Cmdliner

let main interactive width input =
  match
    Format.set_margin width;
    if interactive then Driver.do_repl ~input else Driver.process_file ~input
  with
  | Ok () -> 0
  | Error () -> 1
  | exception (Invalid_argument s) ->
    Format.eprintf "Internal error (invalid argument): %s\n" s;
    1
  | exception (Failure s) ->
    Format.eprintf "Internal error (Failure): %s\n" s;
    1
  | exception (Load.ParseError (err, span)) ->
    let loc = Some span in
    Log.pp_message ~loc ~lvl:`Error Format.pp_print_string Format.std_formatter err;
    1
  | exception (ElabError.ElabError (err, loc)) ->
    Log.pp_message ~loc ~lvl:`Error ElabError.pp Format.std_formatter err;
    1

let opt_interactive =
  let doc = "Interactive mode." in
  Arg.(value & flag & info ["i"; "interactive"] ~doc)

let opt_width =
  let default_width = Format.get_margin () in
  let doc = "Set the maximum output width to VAL columns." in
  Arg.(value & opt int default_width & info ["w"; "width"] ~doc)

let opt_input_file =
  let doc = "The file to typecheck. When FILE is -, read standard input." in
  let parse_dash = Term.(app @@ const @@ fun str -> if str = "-" then None else Some str) in
  Arg.(parse_dash & required & pos ~rev:true 0 (some string) None & info [] ~doc ~docv:"FILE")

let info =
  let doc = "elaborate and normalize terms in Cartesian cubical type theory" in
  let err_exit = Term.exit_info ~doc:"on ill-formed types or terms." 1 in
  Term.info "cooltt" ~version:"0.0" ~doc
    ~exits:(err_exit :: Term.default_exits)

let () =
  let t = Term.(const main $ opt_interactive $ opt_width $ opt_input_file) in
  Term.exit_status @@ Term.eval (t, info)
