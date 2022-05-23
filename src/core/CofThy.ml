open Basis

module Make (Symbol : Symbol.S) =
struct
  module CofVar = CofVar.Make(Symbol)
  include Kado.Theory.Make
      (struct
        type dim = Dim.t
        type var = CofVar.t
        let dim0 = Dim.dim0
        let dim1 = Dim.dim1
        let compare_dim = Dim.compare
        let compare_var = CofVar.compare
      end)
end
