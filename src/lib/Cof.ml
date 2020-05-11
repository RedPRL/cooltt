type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a list
  | Meet of 'a list

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v


let var v = Var v
let bot = Cof (Join [])
let top = Cof (Meet [])

let eq x y =
  if x = y then top else Cof (Eq (x, y))

let join2 phi psi =
  match phi, psi with
  | Cof (Join phis), Cof (Join psis) -> Cof (Join (phis @ psis))
  | Cof (Join []), psi -> psi
  | Cof (Join phis), psi -> Cof (Join ( phis @ [psi]))
  | phi, Cof (Join []) -> phi
  | phi, Cof (Join psis) -> Cof (Join ([phi] @ psis ))
  | phi, psi -> Cof (Join [phi; psi])

let meet2 phi psi =
  match phi, psi with
  | Cof (Meet phis), Cof (Meet psis) -> Cof (Meet (phis @ psis))
  | Cof (Meet []), psi -> psi
  | Cof (Meet phis), psi -> Cof (Meet ( phis @ [psi]))
  | phi, Cof (Meet []) -> phi
  | phi, Cof (Meet psis) -> Cof (Meet ([phi] @ psis ))
  | phi, psi -> Cof (Meet [phi; psi])

let join l = List.fold_left join2 bot l
let meet l = List.fold_left meet2 top l

let rec reduce =
  function
  | Cof (Join phis) -> join (List.map reduce phis)
  | Cof (Meet phis) -> meet (List.map reduce phis)
  | Cof (Eq (r, s)) -> eq r s
  | Var v -> var v
