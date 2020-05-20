exception ParseError of string * CoolBasis.LexingUtil.span

(* Load and parse a file or stdin *)
val load_file : string option -> ConcreteSyntax.signature

val prepare_repl : string option -> in_channel * Lexing.lexbuf
val load_cmd : Lexing.lexbuf -> ConcreteSyntax.command
