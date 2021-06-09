type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a list
  | Meet of 'a list
  | Neg of 'a

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v


let var v = Var v
let bot = Cof (Join [])
let top = Cof (Meet [])

let eq x y =
  if x = y then top else Cof (Eq (x, y))

let join2 phi psi =
  let expose = function Cof (Join phis) -> phis | phi -> [phi] in
  match phi, psi with
  | Cof (Meet []), _ | _, Cof (Meet []) -> Cof (Meet [])
  | phi, psi -> Cof (Join (expose phi @ expose psi))

let meet2 phi psi =
  let expose = function Cof (Meet phis) -> phis | phi -> [phi] in
  match phi, psi with
  | Cof (Join []), _ | _, Cof (Join []) -> Cof (Join [])
  | phi, psi -> Cof (Meet (expose phi @ expose psi))

let join l = List.fold_left join2 bot l
let meet l = List.fold_left meet2 top l

let boundary ~dim0 ~dim1 r = join [eq r dim0; eq r dim1]

let neg_eq ~dim0 ~dim1 r1 r2 =
  join2
    (meet [eq r1 dim0; eq r2 dim1])
    (meet [eq r1 dim1; eq r2 dim0])

let neg phi = Cof (Neg phi)
