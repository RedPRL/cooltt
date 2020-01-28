module CS := ConcreteSyntax
module D := Domain
module S := Syntax

open CoolBasis

type t =
  | UnboundVariable of CS.ident
  | ExpectedEqual of Pp.env * S.tp * S.t * S.t
  | ExpectedEqualTypes of Pp.env * S.tp * S.tp
  | InvalidTypeExpression of CS.t
  | ExpectedConnective of [`Pi | `DimPi | `Sg | `Id | `Nat | `Univ] * D.tp
  | ExpectedSynthesizableTerm of S.t
  | MalformedCase
  | CannotEliminate of Pp.env * S.tp
  | ExpectedSimpleInductive of Pp.env * S.tp

val pp : Format.formatter -> t -> unit

exception ElabError of t