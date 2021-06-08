type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a list
  | Meet of 'a list

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v * bool


let var ?value:(b=true) v = Var (v, b)
let bot = Cof (Join [])
let top = Cof (Meet [])

let eq x y =
  if x = y then top else Cof (Eq (x, y))

let join2 phi psi =
  match phi, psi with
  | Cof (Meet []), _ -> Cof (Meet [])
  | _, Cof (Meet []) -> Cof (Meet [])
  | Cof (Join []), psi -> psi
  | phi, Cof (Join []) -> phi
  | Cof (Join phis), Cof (Join psis) -> Cof (Join (phis @ psis))
  | Cof (Join phis), psi -> Cof (Join (phis @ [psi]))
  | phi, Cof (Join psis) -> Cof (Join ([phi] @ psis ))
  | phi, psi -> Cof (Join [phi; psi])

let meet2 phi psi =
  match phi, psi with
  | Cof (Join []), _ -> Cof (Join [])
  | _, Cof (Join []) -> Cof (Join [])
  | Cof (Meet []), psi -> psi
  | phi, Cof (Meet []) -> phi
  | Cof (Meet phis), Cof (Meet psis) -> Cof (Meet (phis @ psis))
  | Cof (Meet phis), psi -> Cof (Meet (phis @ [psi]))
  | phi, Cof (Meet psis) -> Cof (Meet ([phi] @ psis ))
  | phi, psi -> Cof (Meet [phi; psi])

let join l = List.fold_left join2 bot l
let meet l = List.fold_left meet2 top l

let rec neg ~dim0 ~dim1 =
  function
  | Cof (Eq (r1, r2)) ->
    join2
      (meet [eq r1 dim0; eq r2 dim1])
      (meet [eq r1 dim1; eq r2 dim0])
  | Cof (Meet l) -> join @@ List.map (neg ~dim0 ~dim1) l
  | Cof (Join l) -> meet @@ List.map (neg ~dim0 ~dim1) l
  | Var (v, b) -> Var (v, not b)

let rec reduce =
  function
  | Cof (Join phis) -> join @@ List.map reduce phis
  | Cof (Meet phis) -> meet @@ List.map reduce phis
  | Cof (Eq (r, s)) -> eq r s
  | Var _ as c -> c

let boundary r = join [eq r Dim.Dim0; eq r Dim.Dim1]
