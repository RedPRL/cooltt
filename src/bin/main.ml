open Nbe
open Cmdliner
open Sexplib

exception Internal_failure of string

let mk_fail s = Internal_failure s

let find_idx ~equal key xs =
  let rec go i = function
    | [] -> None
    | x :: xs ->
      if equal key x then Some i else go (i + 1) xs in
  go 0 xs

let slurp_sexps_from_file ~file =
  match Sexp.load_sexps file with
  | [s1; s2] -> (s1, s2)
  | _ ->
    Printf.sprintf "Failed while parsing %s: wrong number of sexps" file
    |> mk_fail
    |> raise
  | exception Sexp.Parse_error {err_msg = msg} ->
    Printf.sprintf "Failed while parsing %s: %s\n" file msg
    |> mk_fail
    |> raise
  | exception Failure _ ->
    Printf.sprintf "Failed while parsing %s: file ended before the sexp was closed\n" file
    |> mk_fail
    |> raise

let syn_of_sexp sexp =
  let exception Illformed in
  let rec syn_of_int = function
    | 0 -> Syn.Zero
    | n -> Syn.Suc (syn_of_int (n - 1)) in
  let rec go env = function
    | Sexp.Atom "Nat" -> Syn.Nat
    | Sexp.Atom "zero" -> Syn.Zero
    | Sexp.Atom var ->
      begin
        match int_of_string_opt var with
        | Some i when i >= 0 -> syn_of_int i
        | _ ->
          match find_idx ~equal:String.equal var env with
          | Some idx -> Syn.Var idx
          | None -> raise Illformed
      end
    | Sexp.List [Sexp.Atom "suc"; t] -> Syn.Suc (go env t)
    | Sexp.List
        [Sexp.Atom "nrec";
         Sexp.List [Sexp.Atom mVar; motive];
         zero;
         Sexp.List [Sexp.Atom pVar; Sexp.Atom indVar; succ];
         n] ->
      Syn.NRec
        (go (mVar :: env) motive,
         go env zero,
         go (indVar :: pVar :: env) succ,
         go env n)
    | Sexp.List [Sexp.Atom "Pi"; src; Sexp.List [Sexp.Atom x; dest]] ->
      Syn.Pi (go env src, go (x :: env) dest)
    | Sexp.List [Sexp.Atom "lam"; Sexp.List [Sexp.Atom x; body]] ->
      Syn.Lam (go (x :: env) body)
    | Sexp.List [Sexp.Atom "ap"; t1; t2] -> Syn.Ap (go env t1, go env t2)
    | Sexp.List [Sexp.Atom "Sig"; src; Sexp.List [Sexp.Atom x; dest]] ->
      Syn.Sig (go env src, go (x :: env) dest)
    | Sexp.List [Sexp.Atom "pair"; l; r] ->
      Syn.Pair (go env l, go env r)
    | Sexp.List [Sexp.Atom "fst"; t] ->
      Syn.Fst (go env t)
    | Sexp.List [Sexp.Atom "snd"; t] ->
      Syn.Snd (go env t)
    | Sexp.List [Sexp.Atom "U"; Sexp.Atom i] ->
      begin
        match int_of_string_opt i with
        | Some i when i >= 0 -> Syn.Uni i
        | _ -> raise Illformed
      end
    | _ -> raise Illformed in
  try go [] sexp with
  | Illformed ->
    Printf.sprintf "Ill-formed terms\n"
    |> mk_fail
    |> raise

let sexp_of_syn t =
  let counter = ref 0 in
  let rec int_of_syn = function
    | Syn.Zero -> Some 0
    | Syn.Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Some (i + 1)
        | None -> None
      end
    | _ -> None in
  let rec go env = function
    | Syn.Var i -> List.nth env i
    | Syn.Nat -> Sexp.Atom "Nat"
    | Syn.Zero -> Sexp.Atom "zero"
    | Syn.Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Sexp.Atom (string_of_int (i + 1))
        | None -> Sexp.List [Sexp.Atom "suc"; go env t]
      end
    | Syn.NRec (motive, zero, suc, n) ->
      incr counter;
      let mvar = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let suc_var1 = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      incr counter;
      let suc_var2 = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List
        [Sexp.Atom "nrec";
         Sexp.List [mvar; go (mvar :: env) motive];
         go env zero;
         Sexp.List [suc_var1; suc_var2; go (suc_var2 :: suc_var1 :: env) suc];
         go env n]
    | Syn.Pi (src, dest) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Pi"; go env src; Sexp.List [var; go (var :: env) dest]]
    | Syn.Lam t ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "lam"; Sexp.List [var; go (var :: env) t]]
    | Syn.Ap (t1, t2) ->
      Sexp.List [Sexp.Atom "ap"; go env t1; go env t2]
    | Syn.Sig (fst, snd) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Sig"; go env fst; Sexp.List [var; go (var :: env) snd]]
    | Syn.Pair (t1, t2) ->
      Sexp.List [Sexp.Atom "pair"; go env t1; go env t2]
    | Syn.Fst t -> Sexp.List [Sexp.Atom "fst"; go env t]
    | Syn.Snd t -> Sexp.List [Sexp.Atom "snd"; go env t]
    | Syn.Uni i -> Sexp.List [Sexp.Atom "U"; Sexp.Atom (string_of_int i)] in
  go [] t


let perform_norm file =
  if String.equal file ""
  then raise (Internal_failure "Failed to supply a file")
  else ();
  let (s1, s2) = slurp_sexps_from_file file in
  let term = syn_of_sexp s1 in
  let tp = syn_of_sexp s2 in
  let norm = normalize ~env:[] ~term ~tp in
  let norm_sexp = sexp_of_syn norm in
  Sexp.output_hum stdout norm_sexp;
  print_newline ();
  0

let main file =
  try perform_norm file with
  | Internal_failure s -> prerr_endline s; 1
  | Nbe_failed s -> Printf.eprintf "Failed to normalize: %s" s; 1

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
