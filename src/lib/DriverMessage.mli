type message =
  | LexingError
  | ParseError
  | NormalizedTerm of {orig : Syntax.t; nf : Syntax.t}
  | Definition of {ident : Ident.t; tp : Syntax.tp; tm : Syntax.t option}
  | UnboundIdent of Ident.t

type error =  DriverError of message * Basis.LexingUtil.span option

val pp_message : Format.formatter -> message -> unit