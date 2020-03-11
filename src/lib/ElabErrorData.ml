module CS = ConcreteSyntax
module S = Syntax
module D = Domain
open CoolBasis

module Data =
struct
  type t =
    | UnboundVariable of CS.ident
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp
    | InvalidTypeExpression of CS.t
    | ExpectedConnective of [`Pi | `Sg | `Id | `Nat | `Univ | `Dim | `Cof | `Sub] * D.tp
    | ExpectedSynthesizableTerm of S.t
    | MalformedCase
    | CannotEliminate of Pp.env * S.tp
    | ExpectedSimpleInductive of Pp.env * S.tp
    | ExpectedDimensionLiteral of int
end