open Normalizer
open Cmdliner
open Sexplib

exception Internal_failure of string

let mk_fail s = Internal_failure s

let slurp_sexps_from_file ~file =
  match Sexp.load_sexps file with
  | [s1; s2] -> (s1, s2)
  | _ ->
    Printf.sprintf "Failed while parsing %s: wrong number of sexps" file
    |> mk_fail
    |> raise
  | exception Sexp.Parse_error {err_msg = msg; _} ->
    Printf.sprintf "Failed while parsing %s: %s\n" file msg
    |> mk_fail
    |> raise
  | exception Failure _ ->
    Printf.sprintf "Failed while parsing %s: file ended before the sexp was closed\n" file
    |> mk_fail
    |> raise

let perform_norm file =
  if String.equal file ""
  then raise (Internal_failure "Failed to supply a file")
  else ();
  let (s1, s2) = slurp_sexps_from_file ~file in
  let term = Syntax.of_sexp s1 in
  let tp = Syntax.of_sexp s2 in
  let () = Check.check ~env:[] ~size:0 ~term ~tp:(Nbe.eval tp []) in
  let norm = Nbe.normalize ~env:[] ~term ~tp in
  let norm_sexp = Syntax.to_sexp [] norm in
  Sexp.output_hum stdout norm_sexp;
  print_newline ();
  0

let main file =
  try perform_norm file with
  | Internal_failure s -> prerr_endline s; 1
  | Invalid_argument s -> Printf.eprintf "Internal error (invalid argument): %s\n" s; 1
  | Failure s -> Printf.eprintf "Internal error (Failure): %s\n" s; 1
  | Check.Cannot_synth t ->
    Printf.eprintf "Found a term in synth position that cannot be synthesized: %s\n" (Syntax.pp t);
    1
  | Check.Type_error -> Printf.eprintf "Type error\n"; 1
  | Check.Cannot_use_var -> Printf.eprintf "Cannot use that variable\n"; 1
  | Syntax.Illformed -> Printf.eprintf "Syntax error.\n"; 1
  | Nbe.Nbe_failed s -> Printf.eprintf "Failed to normalize: %s\n" s; 1

let input_file =
  let doc = "File containing the term to reduce" in
  Arg.(value & pos 0 file "" & info [] ~docv:"input file" ~doc)

let info =
  let doc = "Normalize a term in Martin-Lof Type Theory" in
  let err_exit = Term.exit_info ~doc:"on an ill-formed or terms." 1 in
  Term.info "nbe" ~version:"0.0" ~doc ~exits:(err_exit :: Term.default_exits)

let () =
  let t = Term.(const main $ input_file) in
  Term.exit_status @@ Term.eval (t, info)
