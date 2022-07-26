open Basis

module Make (Symbol : Symbol.S) =
struct
  module CofVar = CofVar.Make (Symbol)
  type t =
    | DDim0
    | DDim1
    | DDimVar of CofVar.t
    | DDimProbe of DimProbe.t

  let equal d1 d2 =
    match d1, d2 with
    | DDim0, DDim0 -> true
    | DDim1, DDim1 -> true
    | DDimVar v1, DDimVar v2 -> Int.equal (CofVar.compare v1 v2) 0
    | DDimProbe p1, DDimProbe p2 -> DimProbe.equal p1 p2
    | _ -> false

  let compare d1 d2 =
    match d1, d2 with
    | DDim0, DDim0 -> 0
    | DDim0, _ -> -1
    | DDim1, DDim0 -> 1
    | DDim1, DDim1 -> 0
    | DDim1, _ -> -1
    | DDimVar _, (DDim0 | DDim1) -> 1
    | DDimVar v1, DDimVar v2 -> CofVar.compare v1 v2
    | DDimVar _, _ -> -1
    | DDimProbe _, (DDim0 | DDim1 | DDimVar _) -> 1
    | DDimProbe p1, DDimProbe p2 -> DimProbe.compare p1 p2

  let ddim0 = DDim0
  let ddim1 = DDim1
  let dvar lvl = DDimVar (CofVar.Local lvl)
  let daxiom sym = DDimVar (CofVar.Axiom sym)

  let dump fmt =
    function
    | DDim0 -> Format.fprintf fmt "dim0"
    | DDim1 -> Format.fprintf fmt "dim1"
    | DDimVar v -> Format.fprintf fmt "dim#var[%a]" CofVar.dump v
    | DDimProbe sym -> Format.fprintf fmt "dim#probe[%a]" DimProbe.pp sym
end
