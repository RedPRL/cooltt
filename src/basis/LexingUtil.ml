include Lexing

type span =
  {start : Lexing.position;
   stop : Lexing.position}

let pp_span : (span * string) Pp.printer =
  fun fmt (span,last_token) ->
  Format.fprintf fmt "%a:%i.%i-%i.%i near %s"
    Uuseg_string.pp_utf_8 span.start.pos_fname
    span.start.pos_lnum
    (span.start.pos_cnum - span.start.pos_bol)
    span.stop.pos_lnum
    (span.stop.pos_cnum - span.stop.pos_bol)
    last_token
