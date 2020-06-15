type error = LexingError of Basis.LexingUtil.span | ParseError of Basis.LexingUtil.span

(* Load and parse a file or stdin *)
val load_file : [`Stdin | `File of string] -> (ConcreteSyntax.signature, error) result

val prepare_repl : unit -> in_channel * Lexing.lexbuf
val load_cmd : Lexing.lexbuf -> (ConcreteSyntax.command, error) result
