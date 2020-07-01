include (module type of Lexing)

type span =
  {start : Lexing.position;
   stop : Lexing.position}

val pp_span : span Pp.printer

val last_token : lexbuf -> string option
val current_span : lexbuf -> span