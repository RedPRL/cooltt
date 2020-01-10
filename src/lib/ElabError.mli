module CS := ConcreteSyntax
module D := Domain
module S := Syntax

open CoolBasis

type t =
  | UnboundVariable of CS.ident
  | ExpectedEqual of Pp.env * S.tp * S.t * S.t
  | ExpectedEqualTypes of Pp.env * S.tp * S.tp
  | InvalidTypeExpression of CS.t
  | ExpectedConnective of [`Pi | `Sg | `Id | `Nat | `Univ] * D.tp
  | ExpectedSynthesizableTerm of S.t

val pp : Format.formatter -> t -> unit

exception ElabError of t