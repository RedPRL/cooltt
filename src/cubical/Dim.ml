open Basis

type t =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of Symbol.t
  | DimGlobal of Symbol.t

let dump fmt =
  function
  | Dim0 -> Format.fprintf fmt "dim0"
  | Dim1 -> Format.fprintf fmt "dim1"
  | DimVar i -> Format.fprintf fmt "dim#var[%i]" i
  | DimProbe sym -> Format.fprintf fmt "dim#probe[%a]" Symbol.pp sym
  | DimGlobal sym -> Format.fprintf fmt "dim#global[%a]" Symbol.pp sym
