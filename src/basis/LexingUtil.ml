include Lexing

type span =
  {start : Lexing.position;
   stop : Lexing.position}

let pp_span : span Pp.printer =
  fun fmt span ->
  Format.fprintf fmt "%a:%i.%i-%i.%i"
    Uuseg_string.pp_utf_8 span.start.pos_fname
    span.start.pos_lnum
    (span.start.pos_cnum - span.start.pos_bol)
    span.stop.pos_lnum
    (span.stop.pos_cnum - span.stop.pos_bol)

let last_token lexbuf = 
  let tok = lexeme lexbuf in
  if tok = "" then None else Some tok

let current_span lexbuf = 
  {start = lexbuf.lex_start_p; stop = lexbuf.lex_curr_p}