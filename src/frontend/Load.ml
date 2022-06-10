open Lex
open Basis

type error =
  | LexingError of {span : LexingUtil.span; last_token : string option}
  | ParseError of {span : LexingUtil.span; last_token : string option}

exception ParseError of string * LexingUtil.span

let parse_with_error parser lexbuf =
  try Ok (parser Lex.token lexbuf) with
  | SyntaxError _msg ->
    let span = LexingUtil.current_span lexbuf in
    let last_token = LexingUtil.last_token lexbuf in
    Error (LexingError {span; last_token})
  | Grammar.Error ->
    let span = LexingUtil.current_span lexbuf in
    let last_token = LexingUtil.last_token lexbuf in
    Error (ParseError {span; last_token})

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
  parse_with_error Grammar.repl_command lexbuf
