type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of DimProbe.t
