module CS := ConcreteSyntax
module D := Domain

type t =
  | UnboundVariable of CS.ident
  | ExpectedEqual of D.tp * D.t * D.t
  | ExpectedEqualTypes of D.tp * D.tp
  | InvalidTypeExpression of CS.t
  | ExpectedConnective of [`Pi | `Sg | `Id | `Nat] * D.tp

val pp : Format.formatter -> t -> unit

exception ElabError of t