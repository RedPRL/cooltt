open Core
open Cmdliner

let execute input = Load.load_file input |> Driver.process_sign

let main input =
  try
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
  | Nbe.NbeFailed s ->
    Format.eprintf "Internal error (Failed to normalize): %s\n" s;
    1
  | ElabError.ElabError (err, _loc) ->
    Format.eprintf "@[<v2>Elaboration error:@;@[<hv>%a@]@]@."
      ElabError.pp err;
    1

let input_file =
  let doc = "File containing the program to type-Ann" in
  Arg.(
    required & pos ~rev:true 0 (some string) None & info [] ~doc ~docv:"FILE")

let info =
  let doc = "Elaborate and normalize terms in Martin-Lof Type Theory" in
  let err_exit = Term.exit_info ~doc:"on an ill-formed types or terms." 1 in
  Term.info "cooltt" ~version:"0.0" ~doc
    ~exits:(err_exit :: Term.default_exits)

let () =
  let t = Term.(const main $ input_file) in
  Term.exit_status @@ Term.eval (t, info)
