open Basis

module Make (Symbol : Symbol.S) =
struct
  module CofVar = CofVar.Make (Symbol)
  type t =
    | Dim0
    | Dim1
    | DimVar of CofVar.t
    | DimProbe of DimProbe.t

  let equal : t -> t -> bool = (=)
  let compare : t -> t -> int = compare

  let dim0 = Dim0
  let dim1 = Dim1
  let var lvl = DimVar (CofVar.Local lvl)
  let axiom sym = DimVar (CofVar.Axiom sym)

  let dump fmt =
    function
    | Dim0 -> Format.fprintf fmt "dim0"
    | Dim1 -> Format.fprintf fmt "dim1"
    | DimVar v -> Format.fprintf fmt "dim#var[%a]" CofVar.dump v
    | DimProbe sym -> Format.fprintf fmt "dim#probe[%a]" DimProbe.pp sym
end
