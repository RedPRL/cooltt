module CS = ConcreteSyntax
module S = Syntax
module D = Domain
open CoolBasis

module Data =
struct

  type connective =
    [ `Pi
    | `Sg
    | `Nat
    | `Univ
    | `Dim
    | `Cof
    | `Sub
    | `Prf
    ]

  type t =
    | UnboundVariable of CS.ident
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t * Conversion.Error.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp * Conversion.Error.t
    | InvalidTypeExpression of CS.t
    | ExpectedConnective of connective * Pp.env * S.tp
    | ExpectedSynthesizableTerm of S.t
    | MalformedCase
    | CannotEliminate of Pp.env * S.tp
    | ExpectedSimpleInductive of Pp.env * S.tp
    | ExpectedDimensionLiteral of int
    | ExpectedTrue of Pp.env * S.t
    | VirtualType

end
