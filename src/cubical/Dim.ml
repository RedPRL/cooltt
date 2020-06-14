open Basis

type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimSym of Symbol.t

