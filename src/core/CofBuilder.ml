open Basis

module Make (Symbol : Symbol.S) =
struct
  module CofVar = CofVar.Make(Symbol)
  module Dim = Dim.Make(Symbol)
  module DDim = DDim.Make(Symbol)

  include Kado.Builder.Free.Make
      (struct
        type dim = Dim.t
        type ddim = DDim.t
        type var = CofVar.t
        let dim0 = Dim.dim0
        let dim1 = Dim.dim1
        let ddim0 = DDim.ddim0
        let ddim1 = DDim.ddim1
        let equal_dim = Dim.equal
        let equal_ddim = DDim.equal
      end)
end
