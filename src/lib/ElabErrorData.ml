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
    | `El
    | `ElV
    ]

  type t =
    | UnboundVariable of Ident.t
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t * Conversion.Error.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp * Conversion.Error.t
    | InvalidTypeExpression of CS.con
    | ExpectedConnective of connective * Pp.env * S.tp
    | ExpectedSynthesizableTerm of CS.con_
    | MalformedCase
    | CannotEliminate of Pp.env * S.tp
    | ExpectedSimpleInductive of Pp.env * S.tp
    | ExpectedDimensionLiteral of int
    | ExpectedTrue of Pp.env * S.t
    | VirtualType

end
