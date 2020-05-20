open Lex
open CoolBasis.LexingUtil

exception ParseError of string * span

let print_position lexbuf =
  let pos = lexbuf.lex_curr_p in
  Printf.sprintf "%s:%d:%d" pos.pos_fname pos.pos_lnum
    (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error parser lexbuf =
  try parser Lex.token lexbuf with
  | SyntaxError msg ->
    let span = {start = lexbuf.lex_start_p; stop = lexbuf.lex_curr_p} in
    raise @@ ParseError ("Lexing error", span)
  | Grammar.Error ->
    let span = {start = lexbuf.lex_start_p; stop = lexbuf.lex_curr_p} in
    raise @@ ParseError ("Parse error", span)

let create_lexbuf input =
  let ch, filename =
    match input with
    | None -> stdin, "[stdin]"
    | Some filename -> open_in filename, filename
  in
  let lexbuf = Lexing.from_channel ch in
  lexbuf.lex_curr_p <- {lexbuf.lex_curr_p with pos_fname = filename};
  ch, lexbuf

let load_file input =
  let ch, lexbuf = create_lexbuf input in
  let sign = parse_with_error Grammar.sign lexbuf in
  close_in ch;
  sign

let prepare_repl input = create_lexbuf input

(* Favonia: still thinking about the line numbers. *)
let reset_pos lexbuf = ()

let load_cmd lexbuf =
  reset_pos lexbuf;
  parse_with_error Grammar.command lexbuf
