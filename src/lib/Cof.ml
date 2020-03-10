type ('r, 'a) cof_f = 
  | Eq of 'r * 'r
  | Join of 'a * 'a 
  | Meet of 'a * 'a
  | Bot 
  | Top

type ('v, 'r) cof = 
  | Cof of ('r, ('v, 'r) cof) cof_f
  | Var of 'v


type 'leaf tree =
  | Const of 'leaf
  | Split of 'leaf tree * 'leaf tree
  | Abort

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

let const leaf = 
  Const leaf

let split t0 t1 =
  match t0, t1 with
  | Abort, t1 -> t1
  | t0, Abort -> t0 
  | t0, t1 -> Split (t0, t1)

let abort = Abort

let rec reduce =
  function
  | Cof Top -> top
  | Cof Bot -> bot
  | Cof (Join (phi, psi)) -> join (reduce phi) (reduce psi)
  | Cof (Meet (phi, psi)) -> meet (reduce phi) (reduce psi)
  | Cof (Eq (r, s)) -> eq r s
  | Var v -> var v


(* TODO: make the output more beautiful *)
let rec pp_cof pp_v pp env fmt =
  function
  | Cof (Eq (x, y)) -> 
    Format.fprintf fmt "%a = %a"
      (pp env) x
      (pp env) y
  | Cof (Join (phi, psi)) ->
    Format.fprintf fmt "(%a) \\/ (%a)"
      (pp_cof pp_v pp env) phi
      (pp_cof pp_v pp env) psi
  | Cof (Meet (phi, psi)) ->
    Format.fprintf fmt "(%a) /\\ (%a)"
      (pp_cof pp_v pp env) phi
      (pp_cof pp_v pp env) psi
  | Cof Bot -> 
    Format.fprintf fmt "false"
  | Cof Top -> 
    Format.fprintf fmt "true"
  | Var v ->
    pp_v env fmt v


let pp_tree pp env fmt = 
  function
  | _ ->
    Format.fprintf fmt "TODO: pp_tree"