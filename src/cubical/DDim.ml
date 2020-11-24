open Basis

type ddim =
  | DDim0
  | DDim1
  | DMeet of ddim * ddim
  | DJoin of ddim * ddim 
  | DDimVar of int
  | DDimSym of Symbol.t