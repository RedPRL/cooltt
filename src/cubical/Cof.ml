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
  | Cof (Meet []), _ | _, Cof (Meet []) -> Cof (Meet [])
  | phi, psi ->
    let expose = function Cof (Join phis) -> phis | phi -> [phi] in
    match expose phi @ expose psi with [phi] -> phi | l -> Cof (Join l)

let meet2 phi psi =
  match phi, psi with
  | Cof (Join []), _ | _, Cof (Join []) -> Cof (Join [])
  | phi, psi ->
    let expose = function Cof (Meet phis) -> phis | phi -> [phi] in
    match expose phi @ expose psi with [phi] -> phi | l -> Cof (Meet l)

let join l = List.fold_left join2 bot l
let meet l = List.fold_left meet2 top l

let boundary ~dim0 ~dim1 r = join [eq r dim0; eq r dim1]

let complexity_cof_f complexity_a =
  function
  | Eq _ -> 1
  | Join l | Meet l -> List.fold_left (fun i c -> i + complexity_a c) 1 l

let rec complexity_cof =
  function
  | Cof cof -> 1 + complexity_cof_f complexity_cof cof
  | Var _ -> 1

let dump_cof_f dump_r dump_a fmt =
  function
  | Eq (r1, r2) -> Format.fprintf fmt "eq[%a;%a]" dump_r r1 dump_r r2
  | Join l ->
    Format.fprintf fmt "join[%a]"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') dump_a) l
  | Meet l ->
    Format.fprintf fmt "meet[%a]"
      (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_char fmt ';') dump_a) l

let rec dump_cof dump_r dump_v fmt =
  function
  | Cof cof -> dump_cof_f dump_r (dump_cof dump_r dump_v) fmt cof
  | Var v -> dump_v fmt v
