{
open Lexing
open Grammar

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with
      pos_bol = lexbuf.lex_curr_pos;
      pos_lnum = pos.pos_lnum + 1
    }

let make_table num elems =
  let table = Hashtbl.create num in
  List.iter (fun (k, v) -> Hashtbl.add table k v) elems;
  table

let keywords =
  make_table 0 [
    ("zero", ZERO);
    ("suc", SUC);
    ("nat", NAT);
    ("let", LET);
    ("in", IN);
    ("fst", FST);
    ("snd", SND);
    ("fun", LAM);
    ("elim", ELIM);
    ("Id", ID);
    ("refl", REFL);
    ("unfold", UNFOLD);
    ("def", DEF);
    ("normalize", NORMALIZE);
    ("quit", QUIT);
    ("univ", UNIV);
    ("dim", DIM);
    ("cof", COF);
    ("sub", SUB);
    ("path", PATH);
    ("coe", COE);
    ("hcom", HCOM);
    ("com", COM)
  ]
}

let line_ending
  = '\r'
  | '\n'
  | "\r\n"
let number =
  ['0'-'9']+
let whitespace =
  [' ' '\t']+
let atom_initial =
  [^ '0'-'9' '-' '?' '!' '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"' '`' ' ' '\t' '\n' '\r']
let atom_subsequent =
  [^                     '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"' ' ' '\t' '\n' '\r']


let number = ['0'-'9']['0'-'9']*
let atom = atom_initial atom_subsequent*

rule token = parse
  | number
    { (NUMERAL (int_of_string (Lexing.lexeme lexbuf))) }
  | ';'
    {comment lexbuf}
  | '('
    { LPR }
  | ')'
    { RPR }
  | '{'
    { LBR }
  | '}'
    { RBR }
  | '['
    { LSQ }
  | ']'
    { RSQ }
  | '|'
    { PIPE }
  | ','
    { COMMA }
  | '*'
    { TIMES }
  | "×"
    { TIMES }
  | ':'
    { COLON }
  | "𝕀"
    { DIM }
  | "∧"
    { MEET }
  | "/\\"
    { MEET }
  | "∨"
    { JOIN }
  | "\\/"
    { JOIN }
  | "="
    { EQUALS }
  | "->"
    { RIGHT_ARROW }
  | "=>"
    { RRIGHT_ARROW }
  | "λ"
    { LAM }
  | "\\"
    { LAM }
  | '_'
    { UNDERSCORE }
  | "?" atom
    {
      match String.split_on_char '?' @@ lexeme lexbuf with
      | [] ->
        HOLE_NAME None
      | _ :: input ->
        let name = String.concat "" input in
        HOLE_NAME (Some name)
    }
  | "?"
    { HOLE_NAME None }
  | "@"
    { AT }
  | "--"
    { comment lexbuf }
  | "#t"
    { TOPC }
  | "#f"
    { BOTC }
  | line_ending
    { new_line lexbuf; token lexbuf }
  | whitespace
    { token lexbuf }
  | eof
    { EOF }
  | atom
    {
      let input = lexeme lexbuf in
      try Hashtbl.find keywords input with
      | Not_found -> Grammar.ATOM input
    }
  | _
    { Printf.eprintf "Unexpected char: %s" (lexeme lexbuf); token lexbuf }
and comment = parse
  | line_ending
    { new_line lexbuf; token lexbuf }
  | _
    { comment lexbuf }
