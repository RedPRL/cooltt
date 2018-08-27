open Normalizer
open Cmdliner
open Sexplib

exception Internal_failure of string

let mk_fail s = raise (Internal_failure s)

let slurp_sexps_from_file ~file =
  let sexps =
    match file with
    (* Want to be on a newline to avoid having output immediately after input *)
    | None -> print_newline (); Sexp.input_sexps stdin
    | Some file -> Sexp.load_sexps file in
  let file =
    match file with
    | Some s -> s
    | None -> "<<stdin>>" in
  match sexps with
  | [s1; s2] -> (s1, s2)
  | _ ->
    Printf.sprintf "Failed while parsing %s: wrong number of sexps" file
    |> mk_fail
  | exception Sexp.Parse_error {err_msg = msg; _} ->
    Printf.sprintf "Failed while parsing %s: %s\n" file msg
    |> mk_fail
  | exception Failure _ ->
    Printf.sprintf "Failed while parsing %s: file ended before the sexp was closed\n" file
    |> mk_fail

let rec process_sign env = function
  | [] -> ()
  | d :: ds ->
    let output = Driver.process_decl env d in
    Driver.output env output;
    process_sign (Driver.update_env env output) ds

let perform_norm input =
  let sign = Load.load_file input in
  process_sign Driver.initial_env sign;
  0

let main input =
  try perform_norm input with
  | Internal_failure s -> prerr_endline s; 1
  | Invalid_argument s -> Printf.eprintf "Internal error (invalid argument): %s\n" s; 1
  | Failure s -> Printf.eprintf "Internal error (Failure): %s\n" s; 1
  | Load.Parse_error s -> Printf.eprintf "Frontend error: %s" s; 1
  | Nbe.Nbe_failed s -> Printf.eprintf "Internal error (Failed to normalize): %s\n" s; 1
  | Check.Type_error e -> Printf.eprintf "Type error\n%s\n" (Check.pp_error e); 1
  | Syntax.Illformed -> Printf.eprintf "Syntax error.\n"; 1

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
