open Core

type output_message =
  | NormalizedTerm of {orig : Syntax.t; nf : Syntax.t}
  | Definition of {ident : Ident.t; tp : Syntax.tp; tm : Syntax.t option}

type error_message =
  | LexingError
  | ParseError
  | UnboundIdent of Ident.t

type message =
  | OutputMessage of output_message
  | ErrorMessage of {error : error_message; last_token : string option}

val pp_message : Format.formatter -> message -> unit
