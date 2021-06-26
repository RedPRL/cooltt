type t =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of DimProbe.t

let dump fmt =
  function
  | Dim0 -> Format.fprintf fmt "dim0"
  | Dim1 -> Format.fprintf fmt "dim1"
  | DimVar i -> Format.fprintf fmt "dim#var[%i]" i
  | DimProbe sym -> Format.fprintf fmt "dim#probe[%a]" DimProbe.pp sym
