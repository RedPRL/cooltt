open Core
open CodeUnit

type output_message =
  | NormalizedTerm of {orig : Syntax.t; nf : Syntax.t}
  | Definition of {ident : Ident.t; tp : Syntax.tp; tm : Syntax.t option}
  | Debug of { ident: Ident.t; tp : Domain.tp; con : Domain.con option }

type warning_message = |

type error_message =
  | LexingError
  | ParseError
  | UnboundIdent of Ident.t
  | InvalidLibrary of string
  | UnitNotFound of string

type message =
  | OutputMessage of output_message
  | WarningMessage of warning_message
  | ErrorMessage of {error : error_message; last_token : string option}

val pp_message : Format.formatter -> message -> unit
