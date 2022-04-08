include Kado.Theory.Make
    (struct
      type dim = Dim.t
      type var = int
      let dim0 = Dim.dim0
      let dim1 = Dim.dim1
      let compare_dim = Dim.compare
      let compare_var = Int.compare
    end)
