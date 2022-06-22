open Basis
open Core

open CodeUnit

module S = Syntax

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


(*
TODO: This is the start of better messaging, still needs work

During Emit, we often don't have a last_token as the parser is happy and we just
have an unbound identifier or a hole or things like that. In those cases, we don't print the
last_token as it would contain nothing.

*)

let pp_message fmt =
  function
  | ErrorMessage {error = ParseError; last_token = None} ->
    Format.fprintf fmt "Parse error"

  | ErrorMessage {error = ParseError; last_token = Some last_token} ->
    Format.fprintf fmt "Parse error near %s" last_token

  | ErrorMessage {error = LexingError; last_token = None} ->
    Format.fprintf fmt "Lexing error"

  | ErrorMessage {error = LexingError; last_token = Some last_token} ->
    Format.fprintf fmt "Lexing error near %s" last_token

  | ErrorMessage {error = UnboundIdent ident; _} ->
    Format.fprintf fmt
      "@[Unbound identifier %a@]"
      Ident.pp ident

  | ErrorMessage {error = InvalidLibrary msg; _} ->
    Format.fprintf fmt
      "@[Could not load the library.@ %a@]" BantorraBasis.Error.pp_lines msg

  | ErrorMessage {error = UnitNotFound msg; _} ->
    Format.fprintf fmt
      "@[Could not find the unit.@ %a@]" BantorraBasis.Error.pp_lines msg

  | WarningMessage _ -> .

  | OutputMessage (NormalizedTerm {orig; nf}) ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[Computed normal form of@ @[<hv>%a@] as@,@[<hv> %a@]@]"
      (Syntax.pp env) orig
      (Syntax.pp env) nf

  | OutputMessage (Definition {ident; tp; ptm = Some (_cof, tm)}) ->
    let env = Pp.Env.emp in
    let _, env' = Pp.Env.bind env None in
    Format.fprintf fmt
      "@[<hov2>def %a :@;@[%a@]@;:=@;%a@]"
      Ident.pp ident
      (Syntax.pp_tp env) tp
      (Syntax.pp env') tm

  | OutputMessage (Definition {ident; tp; ptm = None}) ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[%a : %a@]"
      Ident.pp ident
      (Syntax.pp_tp env) tp
