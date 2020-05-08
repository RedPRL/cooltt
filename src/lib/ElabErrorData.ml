module CS = ConcreteSyntax
module S = Syntax
module D = Domain
open CoolBasis

module Data =
struct

  type connective =
    [ `Pi
    | `Sg
    | `Id
    | `Nat
    | `Univ
    | `Dim
    | `Cof
    | `Sub
    | `Prf
    ]

  type t =
    | UnboundVariable of CS.ident
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp
    | InvalidTypeExpression of CS.con
    | ExpectedConnective of connective * Pp.env * S.tp
    | ExpectedSynthesizableTerm of S.t
    | MalformedCase
    | CannotEliminate of Pp.env * S.tp
    | ExpectedSimpleInductive of Pp.env * S.tp
    | ExpectedDimensionLiteral of int
    | ExpectedTrue of Pp.env * S.t
    | VirtualType
end
