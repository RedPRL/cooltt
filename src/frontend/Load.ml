open Lex
open Basis.LexingUtil

type error = 
  | LexingError of {loc_span : span; last_token: string }
  | ParseError of {loc_span : span; last_token: string }

exception ParseError of string * span

let parse_with_error parser lexbuf =
  try Ok (parser Lex.token lexbuf) with
  | SyntaxError _msg ->
    let span = {start = lexbuf.lex_start_p; stop = lexbuf.lex_curr_p} in
    let last_token = lexeme lexbuf in
    Error (LexingError {loc_span = span;last_token = last_token})
  | Grammar.Error ->
    let span = {start = lexbuf.lex_start_p; stop = lexbuf.lex_curr_p} in
    let last_token = lexeme lexbuf in
    Error (ParseError {loc_span = span;last_token = last_token})

let create_lexbuf input =
  let ch, filename =
    match input with
    | `Stdin -> stdin, "[stdin]"
    | `File filename -> open_in filename, filename
  in
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename};
  ch, lexbuf

let load_file input =
  let ch, lexbuf = create_lexbuf input in
  let sign = parse_with_error Grammar.sign lexbuf in
  close_in ch;
  sign

let prepare_repl () = create_lexbuf `Stdin

(* Favonia: still thinking about the line numbers. *)
let reset_pos _lexbuf = ()

let load_cmd lexbuf =
  reset_pos lexbuf;
  parse_with_error Grammar.command lexbuf
