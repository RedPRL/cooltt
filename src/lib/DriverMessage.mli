(* Driver Messages come in 2 types, either an error message or a normalized term/Definition*)
type output_message =
  | NormalizedTerm of {orig : Syntax.t; nf : Syntax.t}
  | Definition of {ident : Ident.t; tp : Syntax.tp; tm : Syntax.t option}

type error_message =
  | LexingError
  | ParseError
  | UnboundIdent of Ident.t
(*
Either a raw output message or an error type and a last_token string
*)
type message =
  | OutputMessage of output_message
  | ErrorMessage of error_message * string

val pp_message : Format.formatter -> message -> unit