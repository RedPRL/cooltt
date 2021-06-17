open Basis

open CodeUnit

module S = Syntax
module D = Domain

module Data =
struct
  type connective =
    [ `Pi
    | `Sg
    | `Nat
    | `Circle
    | `Univ
    | `Dim
    | `Cof
    | `Sub
    | `Prf
    | `LockedPrf
    | `El
    | `ElV
    | `ElHCom
    | `Record of Ident.t
    ]

  type t =
    | UnboundVariable of Ident.t
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t * Conversion.Error.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp * Conversion.Error.t
    | ExpectedConnective of connective * Pp.env * S.tp
    | ExpectedDimensionLiteral of int
    | ExpectedTrue of Pp.env * S.t
    | VirtualType
    | HoleNotPermitted of Pp.env * S.tp
end
