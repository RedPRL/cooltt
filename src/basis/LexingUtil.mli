include (module type of Lexing)

type span =
  {start : Lexing.position;
   stop : Lexing.position}

val pp_span : (span * string) Pp.printer
