open Basis
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
  | ErrorMessage of {error : error_message; last_token : string}


(*
TODO: This is the start of better messaging, still needs work

During Emit, we often don't have a last_token as the parser is happy and we just
have an unbound identifier or a hole or things like that. In those cases, we don't print the
last_token as it would contain nothing.

*)

let pp_message fmt =
  function
  | ErrorMessage {error = ParseError; last_token} ->
    if last_token = "" then
      Format.pp_print_string fmt "Parse error"
    else
      Format.pp_print_string fmt ("Parse error near " ^ last_token)
  | ErrorMessage {error = LexingError; last_token} ->
    if last_token = "" then
      Format.pp_print_string fmt "Lexing error"
    else
      Format.pp_print_string fmt ("Lexing error near " ^ last_token)
  | OutputMessage (NormalizedTerm {orig; nf}) ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[Computed normal form of@ @[<hv>%a@] as@,@[<hv> %a@]@]"
      (Syntax.pp env) orig
      (Syntax.pp env) nf
  | OutputMessage (Definition {ident; tp; tm = Some tm}) ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[<v>%a@ : %a@ = %a@]"
      Ident.pp ident
      (Syntax.pp_tp env) tp
      (Syntax.pp env) tm
  | OutputMessage (Definition {ident; tp; tm = None}) ->
    let env = Pp.Env.emp in
    Format.fprintf fmt
      "@[%a : %a@]"
      Ident.pp ident
      (Syntax.pp_tp env) tp
  | ErrorMessage {error = UnboundIdent ident; _} ->
    Format.fprintf fmt
      "@[Unbound identifier %a@]"
      Ident.pp ident
