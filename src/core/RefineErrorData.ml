open Basis

open CodeUnit

module S = Syntax
module D = Domain

module Data =
struct
  type connective =
    [ `Pi
    | `Sg
    | `Signature
    | `Data
    | `Nat
    | `Circle
    | `Univ
    | `Desc
    | `Dim
    | `Cof
    | `Sub
    | `Prf
    | `LockedPrf
    | `El
    | `ElV
    | `ElHCom
    ]

  type t =
    | UnboundVariable of Ident.t
    | FieldNameMismatches of Ident.t list * Ident.t list
    | ExpectedField of Pp.env * S.sign * S.t * Ident.t
    | ExpectedCtor of Pp.env * S.tp * Ident.t
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t * Conversion.Error.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp * Conversion.Error.t
    | ExpectedConnective of connective * Pp.env * S.tp
    | ExpectedDimensionLiteral of int
    | ExpectedTrue of Pp.env * S.t
    | VirtualType
    | HoleNotPermitted of Pp.env * S.tp
end
