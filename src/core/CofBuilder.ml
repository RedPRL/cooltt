open Basis

module Make (Symbol : Symbol.S) =
struct
  module CofVar = CofVar.Make(Symbol)

  include Kado.Builder.Free.Make
      (struct
        type dim = Dim.t
        type var = CofVar.t
        let dim0 = Dim.dim0
        let dim1 = Dim.dim1
        let equal_dim = Dim.equal
      end)
end
