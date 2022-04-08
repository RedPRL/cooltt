include Kado.Builder.Free.Make
    (struct
      type dim = Dim.t
      type var = int
      let dim0 = Dim.dim0
      let dim1 = Dim.dim1
      let equal_dim = Dim.equal
    end)
