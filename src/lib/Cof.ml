type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a * 'a
  | Meet of 'a * 'a
  | Bot
  | Top

type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v


let var v = Var v
let bot = Cof Bot
let top = Cof Top

let eq x y =
  if x = y then top else Cof (Eq (x, y))

let join phi psi =
  match phi, psi with
  | Cof Top, _ -> top
  | _, Cof Top -> top
  | Cof Bot, psi -> psi
  | phi, Cof Bot -> phi
  | phi, psi -> Cof (Join (phi, psi))

let meet phi psi =
  match phi, psi with
  | Cof Top, phi -> phi
  | phi, Cof Top -> phi
  | Cof Bot, phi -> bot
  | phi, Cof Bot -> bot
  | phi, psi -> Cof (Meet (phi, psi))


let rec nmeet =
  function
  | [] ->
    Cof Top
  | phi :: phis ->
    meet phi @@ nmeet phis


let rec reduce =
  function
  | Cof Top -> top
  | Cof Bot -> bot
  | Cof (Join (phi, psi)) -> join (reduce phi) (reduce psi)
  | Cof (Meet (phi, psi)) -> meet (reduce phi) (reduce psi)
  | Cof (Eq (r, s)) -> eq r s
  | Var v -> var v


(* TODO: make the output even more beautiful *)
let rec pp_cof pp_v pp env fmt =
  function
  | Cof (Eq (x, y)) ->
    Format.fprintf fmt "%a = %a"
      (pp env) x
      (pp env) y
  | Cof (Join (phi, psi)) ->
    Format.fprintf fmt "(%a) %a (%a)"
      (pp_cof pp_v pp env) phi
      Uuseg_string.pp_utf_8 "∨"
      (pp_cof pp_v pp env) psi
  | Cof (Meet (phi, psi)) ->
    Format.fprintf fmt "(%a) %a (%a)"
      (pp_cof pp_v pp env) phi
      Uuseg_string.pp_utf_8 "∧"
      (pp_cof pp_v pp env) psi
  | Cof Bot ->
    Format.fprintf fmt "false"
  | Cof Top ->
    Format.fprintf fmt "true"
  | Var v ->
    pp_v env fmt v
