module CS := ConcreteSyntax
module D := Domain
module S := Syntax

type t =
  | UnboundVariable of CS.ident
  | ExpectedEqual of D.tp * D.con * D.con
  | ExpectedEqualTypes of D.tp * D.tp
  | InvalidTypeExpression of CS.t
  | ExpectedConnective of [`Pi | `Sg | `Id | `Nat] * D.tp
  | ExpectedSynthesizableTerm of S.t

val pp : Format.formatter -> t -> unit

exception ElabError of t