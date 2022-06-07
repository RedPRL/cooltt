open Basis
open Core

open CodeUnit

module CS := ConcreteSyntax
module S := Syntax

type t =
  | MalformedCase
  | InvalidTypeExpression of CS.con
  | ExpectedSynthesizableTerm of CS.con_
  | CannotEliminate of Pp.env * S.tp
  | ExpectedSimpleInductive of Pp.env * S.tp
  | InvalidModifier of CS.con
  | ExpectedFailure of CS.decl

val pp : Format.formatter -> t -> unit

exception ElabError of t * LexingUtil.span option
