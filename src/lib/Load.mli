exception Parse_error of string

(* Load and parse a file or stdin *)
val load : string option -> ConcreteSyntax.signature
