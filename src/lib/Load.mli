exception ParseError of string * CoolBasis.LexingUtil.span

(* Load and parse a file or stdin *)
val load : string option -> ConcreteSyntax.signature
