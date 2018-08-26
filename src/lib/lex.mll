{
open Lexing
open Grammar

exception SyntaxError of string

let next_line lexbuf =
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <-
    { pos with pos_bol = lexbuf.lex_curr_pos;
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
    ("Nat", NAT);
    ("let", LET);
    ("in", IN);
    ("with", WITH);
    ("end", END);
    ("Later", LATER);
    ("next", NEXT);
    ("rec", REC);
    ("Box", BOX);
    ("shut", SHUT);
    ("open", OPEN);
    ("fst", FST);
    ("snd", SND);
    ("lam", LAM);
    ("next", NEXT);
    ("dfix", DFIX);
    ("U", UNIV);
    ("def", DEF);
    ("at", AT);
    ("normalize", NORMALIZE);
    ("quit", QUIT);
  ]
}

let number = ['0'-'9']['0'-'9']*
let whitespace = [' ' '\t']+
let line_ending = '\r' | '\n' | "\r\n"
let atom_first = ['a'-'z' 'A'-'Z' '_']
let atom_next = ['a'-'z' 'A'-'Z' '_' '-' '*' '/']
let atom = atom_first atom_next*

rule token = parse
  | number
    { (NUMERAL (int_of_string (Lexing.lexeme lexbuf))) }
  | ';'
    {comment lexbuf}
  | '('
    { LPR }
  | ')'
    { RPR }
  | '['
    { LBR }
  | ']'
    { RBR }
  | '|'
    { PIPE }
  | '*'
    { TIMES }
  | "×"
    { TIMES }
  | ':'
    { COLON }
  | '.'
    { DOT }
  | "="
    { EQUALS }
  | "->"
    { RIGHT_ARROW }
  | "<"
    { LANGLE }
  | ">"
    { RANGLE }
  | "λ"
    { LAM }
  | '_'
    { UNDERSCORE }
  | line_ending
    { new_line lexbuf; token lexbuf }
  | whitespace
    { token lexbuf }
  | eof
    { EOF }
  | atom
    {
      let input = lexeme lexbuf in
      begin try
        let kwd = Hashtbl.find keywords input in
        kwd
      with Not_found ->
        (Grammar.ATOM input)
      end
    }
  | _
    { Printf.eprintf "Unexpected char: %s" (lexeme lexbuf); token lexbuf }
and comment = parse
  | line_ending
    { new_line lexbuf; token lexbuf }
  | _
    { comment lexbuf }
