open Normalizer
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
  | exception Sexp.Parse_error {err_msg = msg; _} ->
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
    | 0 -> Syntax.Zero
    | n -> Syntax.Suc (syn_of_int (n - 1)) in
  let rec go env = function
    | Sexp.Atom "Nat" -> Syntax.Nat
    | Sexp.Atom "zero" -> Syntax.Zero
    | Sexp.Atom "<>" -> Syntax.Bullet
    | Sexp.Atom var ->
      begin
        match int_of_string_opt var with
        | Some i when i >= 0 -> syn_of_int i
        | _ ->
          match find_idx ~equal:String.equal var env with
          | Some idx -> Syntax.Var idx
          | None -> raise Illformed
      end
    | Sexp.List [Sexp.Atom "suc"; t] -> Syntax.Suc (go env t)
    | Sexp.List
        [Sexp.Atom "nrec";
         Sexp.List [Sexp.Atom mVar; motive];
         zero;
         Sexp.List [Sexp.Atom pVar; Sexp.Atom indVar; succ];
         n] ->
      Syntax.NRec
        (go (mVar :: env) motive,
         go env zero,
         go (indVar :: pVar :: env) succ,
         go env n)
    | Sexp.List [Sexp.Atom "let"; Sexp.List [Sexp.Atom x; arg]; body] ->
      Syntax.Ap (Syntax.Lam (go (x :: env) body), go env arg)
    | Sexp.List [Sexp.Atom "Pi"; src; Sexp.List [Sexp.Atom x; dest]] ->
      Syntax.Pi (go env src, go (x :: env) dest)
    | Sexp.List [Sexp.Atom "lam"; Sexp.List [Sexp.Atom x; body]] ->
      Syntax.Lam (go (x :: env) body)
    | Sexp.List (Sexp.Atom "ap" :: f :: args) ->
      List.fold_left (fun f a -> Syntax.Ap (f, go env a)) (go env f) args
    | Sexp.List [Sexp.Atom "Sig"; src; Sexp.List [Sexp.Atom x; dest]] ->
      Syntax.Sig (go env src, go (x :: env) dest)
    | Sexp.List [Sexp.Atom "pair"; l; r] ->
      Syntax.Pair (go env l, go env r)
    | Sexp.List [Sexp.Atom "fst"; t] ->
      Syntax.Fst (go env t)
    | Sexp.List [Sexp.Atom "snd"; t] ->
      Syntax.Snd (go env t)
    | Sexp.List [Sexp.Atom "Later"; Sexp.List [Sexp.Atom x; t]] ->
      Syntax.Later (go (x :: env) t)
    | Sexp.List [Sexp.Atom "next"; Sexp.List [Sexp.Atom x; t]] ->
      Syntax.Next (go (x :: env) t)
    | Sexp.List [Sexp.Atom "prev"; term; tick] ->
      Syntax.Prev (go env term, go env tick)
    | Sexp.List [Sexp.Atom "Box"; t] ->
      Syntax.Box (go env t)
    | Sexp.List [Sexp.Atom "open"; t] ->
      Syntax.Open (go env t)
    | Sexp.List [Sexp.Atom "shut"; t] ->
      Syntax.Shut (go env t)
    | Sexp.List [Sexp.Atom "dfix"; tp; Sexp.List [Sexp.Atom x; body]] ->
      Syntax.DFix (go env tp, go (x :: env) body)
    | Sexp.List [Sexp.Atom "U"; Sexp.Atom i] ->
      begin
        match int_of_string_opt i with
        | Some i when i >= 0 -> Syntax.Uni i
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
    | Syntax.Zero -> Some 0
    | Syntax.Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Some (i + 1)
        | None -> None
      end
    | _ -> None in
  let rec go env = function
    | Syntax.Var i -> List.nth env i
    | Syntax.Nat -> Sexp.Atom "Nat"
    | Syntax.Zero -> Sexp.Atom "zero"
    | Syntax.Suc t ->
      begin
        match int_of_syn t with
        | Some i -> Sexp.Atom (string_of_int (i + 1))
        | None -> Sexp.List [Sexp.Atom "suc"; go env t]
      end
    | Syntax.NRec (motive, zero, suc, n) ->
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
    | Syntax.Pi (src, dest) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Pi"; go env src; Sexp.List [var; go (var :: env) dest]]
    | Syntax.Lam t ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "lam"; Sexp.List [var; go (var :: env) t]]
    | Syntax.Ap (t1, t2) ->
      Sexp.List [Sexp.Atom "ap"; go env t1; go env t2]
    | Syntax.Sig (fst, snd) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Sig"; go env fst; Sexp.List [var; go (var :: env) snd]]
    | Syntax.Pair (t1, t2) ->
      Sexp.List [Sexp.Atom "pair"; go env t1; go env t2]
    | Syntax.Fst t -> Sexp.List [Sexp.Atom "fst"; go env t]
    | Syntax.Snd t -> Sexp.List [Sexp.Atom "snd"; go env t]
    | Syntax.Uni i -> Sexp.List [Sexp.Atom "U"; Sexp.Atom (string_of_int i)]
    | Syntax.Later t ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Later"; Sexp.List [var; go (var :: env) t]]
    | Syntax.Next t ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "Next"; Sexp.List [var; go (var :: env) t]]
    | Syntax.Prev (term, tick) ->
      Sexp.List [Sexp.Atom "prev"; go env term; go env tick]
    | Syntax.Bullet -> Sexp.Atom "<>"
    | Syntax.Box t -> Sexp.List [Sexp.Atom "Box"; go env t]
    | Syntax.Open t -> Sexp.List [Sexp.Atom "open"; go env t]
    | Syntax.Shut t -> Sexp.List [Sexp.Atom "shut"; go env t]
    | Syntax.DFix (tp, body) ->
      incr counter;
      let var = Sexp.Atom ("x" ^ string_of_int (! counter)) in
      Sexp.List [Sexp.Atom "dfix"; go env tp; Sexp.List [var; go (var :: env) body]] in
  go [] t


let perform_norm file =
  if String.equal file ""
  then raise (Internal_failure "Failed to supply a file")
  else ();
  let (s1, s2) = slurp_sexps_from_file ~file in
  let term = syn_of_sexp s1 in
  let tp = syn_of_sexp s2 in
  let norm = Nbe.normalize ~env:[] ~term ~tp in
  let norm_sexp = sexp_of_syn norm in
  Sexp.output_hum stdout norm_sexp;
  print_newline ();
  0

let main file =
  try perform_norm file with
  | Internal_failure s -> prerr_endline s; 1
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
