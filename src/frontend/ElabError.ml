open Basis
open Core

open CodeUnit

module CS = ConcreteSyntax
module S = Syntax

type t =
  | MalformedCase
  | InvalidTypeExpression of CS.con
  | ExpectedSynthesizableTerm of CS.con_
  | CannotEliminate of Pp.env * S.tp
  | ExpectedSimpleInductive of Pp.env * S.tp
  | InvalidModifier of CS.con


let pp fmt =
  function
  | ExpectedSynthesizableTerm orig ->
    Format.fprintf fmt
      "@[Type annotation required for@,@[<hv> %a@]@]"
      CS.pp_con_ orig
  | InvalidTypeExpression cs ->
    Format.fprintf fmt
      "Invalid type expression: %a"
      CS.pp_con cs
  | MalformedCase ->
    Format.fprintf fmt "Malformed case"
  | CannotEliminate (ppenv, tp) ->
    Format.fprintf fmt
      "Cannot eliminate element of type %a"
      (S.pp_tp ppenv) tp
  | ExpectedSimpleInductive (ppenv, tp) ->
    Format.fprintf fmt
      "Expected simple inductive type but found %a"
      (S.pp_tp ppenv) tp
  | InvalidModifier cs ->
    Format.fprintf fmt
      "Invalid modifier: %a"
      CS.pp_con cs

exception ElabError of t * LexingUtil.span option

let _ =
  PpExn.install_printer @@ fun fmt ->
  function
  | ElabError (err, _loc) ->
    pp fmt err
  | _ ->
    raise PpExn.Unrecognized
