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
    ("locked", LOCKED);
    ("unlock", UNLOCK);
    ("zero", ZERO);
    ("suc", SUC);
    ("nat", NAT);
    ("base", BASE);
    ("loop", LOOP);
    ("circle", CIRCLE);
    ("🍪", CIRCLE);
    ("let", LET);
    ("in", IN);
    ("fst", FST);
    ("snd", SND);
    ("elim", ELIM);
    ("unfold", UNFOLD);
    ("generalize", GENERALIZE);
    ("def", DEF);
    ("axiom", AXIOM);
    ("normalize", NORMALIZE);
    ("print", PRINT);
    ("quit", QUIT);
    ("type", TYPE);
    ("𝕀", DIM);
    ("dim", DIM);
    ("lvl", LVL);
    ("𝔽", COF);
    ("cof", COF);
    ("sub", SUB);
    ("ext", EXT);
    ("coe", COE);
    ("hcom", HCOM);
    ("hfill", HFILL);
    ("com", COM);
    ("V", V);
    ("🥦", V);
    ("vproj", VPROJ);
    ("cap", CAP);
    ("with", WITH);
    ("import",IMPORT []);
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
  [^ '0'-'9' '-'     '?' '!' '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"' '`' ' ' '\t' '\n' '\r']
let atom_subsequent =
  [^                         '(' ')' '[' ']' '{' '}' '<' '>' '.' '#' '\\' '@' '*' '^' ':' ',' ';' '|' '=' '"'     ' ' '\t' '\n' '\r']
let atom = atom_initial atom_subsequent*

let module_part =
  [^             '/' '?' '!' '(' ')' '[' ']' '{' '}' '<' '>' '.'     '\\'     '*'     ':' ',' ';' '|' '=' '"' '`' ' ' '\t' '\n' '\r']+

let hole_atom_initial
  = atom_initial
  | '?'

let hole_atom_subsequent
  = atom_subsequent
  | '?'

let hole_atom = hole_atom_initial hole_atom_subsequent*

rule token = parse "" { skip_whitespace real_token lexbuf }

and skip_whitespace kont = parse
  | "--" | "⍝" (* APL *)
    { line_comment (skip_whitespace kont) lexbuf }
  | "/-"
    { block_comment (skip_whitespace kont) lexbuf }
  | line_ending
    { new_line lexbuf; (skip_whitespace kont) lexbuf }
  | whitespace
    { skip_whitespace kont lexbuf }
  | ""
    { kont lexbuf }

and real_token = parse
  | number
    { NUMERAL (int_of_string (Lexing.lexeme lexbuf)) }
  | "⨾" | ";;"
    { SEMISEMI }
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
  | '.'
    { DOT }
  | ";"
    { SEMI }
  | "×" | '*'
    { TIMES }
  | ':'
    { COLON }
  | "∧" | "/\\"
    { MEET }
  | "∨" | "\\/"
    { JOIN }
  | "="
    { EQUALS }
  | "≔" | ":="
    { COLON_EQUALS }
  | "→" | "->"
    { RIGHT_ARROW }
  | "⇒" | "=>"
    { RRIGHT_ARROW }
  | '_'
    { UNDERSCORE }
  | "?" hole_atom
    {
      let str = lexeme lexbuf in
      let len = String.length str in
      if len = 1 then
        HOLE_NAME None
      else
        let hole_name = String.sub str 1 (String.length str - 1) in
        HOLE_NAME (Some hole_name)
    }
  | "?"
    { HOLE_NAME None }
  | "!"
    { BANG }
  | "∂" (* XXX what to do with "∂i"? *)
    { BOUNDARY }
  | "#t" (* XXX what to do with "#txyz"? *)
    { TOPC }
  | "#f" (* XXX what to do with "#fxyz"? *)
    { BOTC }
  | eof
    { EOF }
  | atom
    {
      let input = lexeme lexbuf in
      match Hashtbl.find keywords input with
      | IMPORT _ -> import_path [] lexbuf
      | tok -> tok
      | exception Not_found -> Grammar.ATOM input
    }
  | _
    { Printf.eprintf "Unexpected char: %s" (lexeme lexbuf); token lexbuf }

and import_path rev_path = parse "" { skip_whitespace (real_import_path rev_path) lexbuf }

and real_import_path rev_path = parse
  | module_part
    { dot_import_path (lexeme lexbuf :: rev_path) lexbuf }
  | _
    { Printf.eprintf "Expected unit path: %s" (lexeme lexbuf); token lexbuf }

and dot_import_path rev_path = parse "" { skip_whitespace (real_dot_import_path rev_path) lexbuf }

and real_dot_import_path rev_path = parse
  | '.'
    { import_path rev_path lexbuf }
  | ""
    { IMPORT (List.rev rev_path) }

and line_comment kont = parse
  | line_ending
    { new_line lexbuf; kont lexbuf }
  | _
    { line_comment kont lexbuf }

and block_comment kont = parse
  | "/-"
    { block_comment (block_comment kont) lexbuf }
  | "-/"
    { kont lexbuf }
  | line_ending
    { new_line lexbuf; block_comment kont lexbuf }
  | _
    { block_comment kont lexbuf }
