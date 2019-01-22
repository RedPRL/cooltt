open Normalizer
open Cmdliner

let perform_norm input = Load.load_file input |> Driver.process_sign

let main input =
  try perform_norm input; 0 with
  | Invalid_argument s -> Printf.eprintf "Internal error (invalid argument): %s\n" s; 1
  | Failure s -> Printf.eprintf "Internal error (Failure): %s\n" s; 1
  | Load.Parse_error s -> Printf.eprintf "Frontend error: %s" s; 1
  | Nbe.Nbe_failed s -> Printf.eprintf "Internal error (Failed to normalize): %s\n" s; 1
  | Check.Type_error e -> Printf.eprintf "Type error:\n"; Check.pp_error Format.err_formatter e; 1

let input_file =
  let doc = "File containing the term to reduce" in
  Arg.(value & pos 0 file "" & info [] ~docv:"input file" ~doc)

let info =
  let doc = "Typecheck and Normalize a term in Guarded Martin-Lof Type Theory" in
  let err_exit = Term.exit_info ~doc:"on an ill-formed or terms." 1 in
  Term.info "blott" ~version:"0.0" ~doc ~exits:(err_exit :: Term.default_exits)

let () =
  let t = Term.(const main $ input_file) in
  Term.exit_status @@ Term.eval (t, info)
