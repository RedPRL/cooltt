open Basis

module Make (Symbol : Symbol.S) =
struct
  module CofVar = CofVar.Make (Symbol)
  type t =
    | Dim0
    | Dim1
    | DimVar of CofVar.t
    | DimProbe of DimProbe.t

  let equal d1 d2 =
    match d1, d2 with
    | Dim0, Dim0 -> true
    | Dim1, Dim1 -> true
    | DimVar v1, DimVar v2 -> Int.equal (CofVar.compare v1 v2) 0
    | DimProbe p1, DimProbe p2 -> DimProbe.equal p1 p2
    | _ -> false

  let compare d1 d2 =
    match d1, d2 with
    | Dim0, Dim0 -> 0
    | Dim0, _ -> -1
    | Dim1, Dim0 -> 1
    | Dim1, Dim1 -> 0
    | Dim1, _ -> -1
    | DimVar _, (Dim0 | Dim1) -> 1
    | DimVar v1, DimVar v2 -> CofVar.compare v1 v2
    | DimVar _, _ -> -1
    | DimProbe _, (Dim0 | Dim1 | DimVar _) -> 1
    | DimProbe p1, DimProbe p2 -> DimProbe.compare p1 p2

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
