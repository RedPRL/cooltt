open Basis

type output_message =
  | NormalizedTerm of {orig : Syntax.t; nf : Syntax.t}
  | Definition of {ident : Ident.t; tp : Syntax.tp; tm : Syntax.t option}

type error_message =
  | LexingError
  | ParseError
  | UnboundIdent of Ident.t

type message =
  | OutputMessage of output_message
  | ErrorMessage of error_message * string


(* TODO: This is the start of better messaging, still needs work *)

let pp_message fmt =
  function
  | ErrorMessage (ParseError,last_token) ->
    if last_token = "" then
      Format.pp_print_string fmt "Parse error"
    else
      Format.pp_print_string fmt ("Parse error near " ^ last_token)
  | ErrorMessage (LexingError,last_token) ->
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
  | ErrorMessage ((UnboundIdent ident),_) ->
    Format.fprintf fmt
      "@[Unbound identifier %a@]"
      Ident.pp ident
