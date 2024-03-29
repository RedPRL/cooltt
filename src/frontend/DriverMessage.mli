open Core
open CodeUnit

type output_message =
  | NormalizedTerm of {orig : Syntax.t; nf : Syntax.t}
  | Definition of {ident : Ident.t; tp : Syntax.tp; ptm : (Syntax.t * Syntax.t) option}

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
