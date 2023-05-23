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
    | `Nat
    | `Circle
    | `Univ
    | `Dim
    | `Cof
    | `Sub
    | `Prf
    | `El
    | `ElV
    | `ElHCom
    | `ElExt
    ]

  type t =
    | UnboundVariable of Ident.t
    | FieldNameMismatches of Ident.user list * Ident.user list
    | ExpectedField of Pp.env * S.tele * S.t * Ident.t
    | ExpectedEqual of Pp.env * S.tp * S.t * S.t * Conversion.Error.t
    | ExpectedEqualTypes of Pp.env * S.tp * S.tp * Conversion.Error.t
    | ExpectedConnective of connective * Pp.env * S.tp
    | ExpectedDimensionLiteral of int
    | ExpectedTrue of Pp.env * S.t
    | VirtualType
    | HoleNotPermitted of Pp.env * S.tp
    | BindingNotFound of Ident.user
    | UnexpectedShadowing of Ident.user
    | CyclicImport of CodeUnitID.t
    | ErrorsInSection
    | UnsolvedHoles of int
    | ExpectedSignature of Pp.env * S.t
    | ExpectedStructure of Pp.env * S.t
end
