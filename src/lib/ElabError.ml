module CS = ConcreteSyntax
module D = Domain
module S = Syntax
open CoolBasis

type t =
  | UnboundVariable of CS.ident
  | ExpectedEqual of Pp.env * S.tp * S.t * S.t
  | ExpectedEqualTypes of D.tp * D.tp
  | InvalidTypeExpression of CS.t
  | ExpectedConnective of [`Pi | `Sg | `Id | `Nat | `Univ] * D.tp
  | ExpectedSynthesizableTerm of S.t


module Fmt = Format
let pp fmt =
  function
  | UnboundVariable id -> 
    Fmt.fprintf fmt "Unbound variable %a" Uuseg_string.pp_utf_8 id
  | ExpectedEqual (ppenv, tp, tm0, tm1) ->
    Fmt.fprintf fmt
      "Expected @[<hv>%a@;= %a@;: %a@]"
      (S.pp_ ppenv) tm0
      (S.pp_ ppenv) tm1
      (S.pp_tp_ ppenv) tp
  | ExpectedEqualTypes (_tp0, _tp1) ->
    Fmt.fprintf fmt 
      "Type mismatch"
  | ExpectedConnective _ ->
    Fmt.fprintf fmt 
      "Head connective mismatch"
  | ExpectedSynthesizableTerm _ ->
    Fmt.fprintf fmt 
      "Expected synthesizable term"
  | InvalidTypeExpression cs ->
    Fmt.fprintf fmt 
      "Invalid type expression: %a"
      CS.pp cs


exception ElabError of t

let _ = 
  PpExn.install_printer @@ fun fmt ->
  function 
  | ElabError err ->
    pp fmt err 
  | _ -> 
    raise PpExn.Unrecognized