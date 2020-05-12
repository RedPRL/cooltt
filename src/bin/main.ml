open Core
open Cmdliner

let execute input = Load.load input |> Driver.process_sign

let main width input =
  try
    Format.set_margin width;
    execute input;
    0
  with
  | Invalid_argument s ->
    Format.eprintf "Internal error (invalid argument): %s\n" s;
    1
  | Failure s ->
    Format.eprintf "Internal error (Failure): %s\n" s;
    1
  | Load.Parse_error s ->
    Format.eprintf "Frontend error: %s" s;
    1
  | ElabError.ElabError (err, loc) ->
    Log.pp_message ~loc ~lvl:`Error ElabError.pp Format.err_formatter err;
    1

let opt_width =
  let default_width = Format.get_margin () in
  let doc = "Set the maximum output width to VAL columns." in
  Arg.(value & opt int default_width & info ["w"; "width"] ~doc)

let opt_input_file =
  let doc = "The file to typecheck. With no FILE, read standard input." in
  Arg.(value & pos ~rev:true 0 (some string) None & info [] ~doc ~docv:"FILE")

let info =
  let doc = "elaborate and normalize terms in Cartesian cubical type theory" in
  let err_exit = Term.exit_info ~doc:"on ill-formed types or terms." 1 in
  Term.info "cooltt" ~version:"0.0" ~doc
    ~exits:(err_exit :: Term.default_exits)

let () =
  let t = Term.(const main $ opt_width $ opt_input_file) in
  Term.exit_status @@ Term.eval (t, info)
