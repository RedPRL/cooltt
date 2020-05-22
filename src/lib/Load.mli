type error = LexingError of CoolBasis.LexingUtil.span | ParseError of CoolBasis.LexingUtil.span

(* Load and parse a file or stdin *)
val load_file : string option -> (ConcreteSyntax.signature, error) result

val prepare_repl : string option -> in_channel * Lexing.lexbuf
val load_cmd : Lexing.lexbuf -> (ConcreteSyntax.command, error) result
