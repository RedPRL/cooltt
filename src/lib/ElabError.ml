module CS = ConcreteSyntax
module D = Domain
module S = Syntax
open CoolBasis

type t =
  | UnboundVariable of CS.ident
  | ExpectedEqual of Pp.env * S.tp * S.t * S.t
  | ExpectedEqualTypes of Pp.env * S.tp * S.tp
  | InvalidTypeExpression of CS.t
  | ExpectedConnective of [`Pi | `Sg | `Id | `Nat | `Univ] * D.tp
  | ExpectedSynthesizableTerm of S.t
  | MalformedCase
  | CannotEliminate of Pp.env * S.tp
  | ExpectedSimpleInductive of Pp.env * S.tp


module Fmt = Format
let pp fmt =
  function
  | UnboundVariable id -> 
    Fmt.fprintf fmt "Unbound variable %a" Uuseg_string.pp_utf_8 id
  | ExpectedEqual (ppenv, tp, tm0, tm1) ->
    Fmt.fprintf fmt
      "Expected @[<hv>%a =@;%a@;: %a@]"
      (S.pp ppenv) tm0
      (S.pp ppenv) tm1
      (S.pp_tp ppenv) tp
  | ExpectedEqualTypes (ppenv, tp0, tp1) ->
    Fmt.fprintf fmt
      "Expected @[<hv>%a =@;%a@]"
      (S.pp_tp ppenv) tp0
      (S.pp_tp ppenv) tp1
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
  | MalformedCase ->
    Fmt.fprintf fmt "Malformed case"
  | CannotEliminate (ppenv, tp) ->
    Fmt.fprintf fmt 
      "Cannot eliminate element of type %a"
      (S.pp_tp ppenv) tp
  | ExpectedSimpleInductive (ppenv, tp) ->
    Fmt.fprintf fmt 
      "Expected simple inductive type but found %a"
      (S.pp_tp ppenv) tp


exception ElabError of t

let _ = 
  PpExn.install_printer @@ fun fmt ->
  function 
  | ElabError err ->
    pp fmt err 
  | _ -> 
    raise PpExn.Unrecognized