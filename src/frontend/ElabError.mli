open Basis 
open Core
module CS := ConcreteSyntax
module S := Syntax

type t =
  | MalformedCase
  | InvalidTypeExpression of CS.con
  | ExpectedSynthesizableTerm of CS.con_
  | CannotEliminate of Pp.env * S.tp
  | ExpectedSimpleInductive of Pp.env * S.tp

val pp : Format.formatter -> t -> unit

exception ElabError of t * LexingUtil.span option
