open Basis

type ddim =
  | DDim0
  | DDim1
  | DDimVar of int
  | DDimSym of Symbol.t