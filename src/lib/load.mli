exception Parse_error of string

(* Load and parse a file *)
val load_file : string -> Concrete_syntax.signature
