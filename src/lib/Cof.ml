type ('v, 'a) cof = 
  | Var of 'v
  | Eq of 'a * 'a
  | Join of ('v, 'a) cof * ('v, 'a) cof
  | Meet of ('v, 'a) cof * ('v, 'a) cof
  | Bot
  | Top


type ('v, 'a, 'b) tree =
  | Const of ('v, 'a) cof * 'b
  | Split of ('v, 'a, 'b) tree * ('v, 'a, 'b) tree
  | Abort

let var v = Var v
let bot = Bot
let top = Top

let eq x y = 
  if x = y then top else Eq (x, y)

let join phi psi = 
  match phi, psi with 
  | Top, _ -> Top
  | _, Top -> Top 
  | Bot, psi -> psi
  | phi, Bot -> phi
  | phi, psi -> Join (phi, psi)

let meet phi psi =
  match phi, psi with
  | Top, phi -> phi
  | phi, Top -> phi
  | Bot, phi -> Bot 
  | phi, Bot -> Bot 
  | phi, psi -> Meet (phi, psi)

let const psi x = 
  match psi with 
  | Bot -> Abort
  | _ ->
    Const (psi, x)

let split t0 t1 =
  match t0, t1 with
  | Abort, t1 -> t1
  | t0, Abort -> t0 
  | t0, t1 -> Split (t0, t1)

let abort = Abort

let rec reduce =
  function
  | Top -> top
  | Bot -> bot
  | Join (phi, psi) -> join (reduce phi) (reduce psi)
  | Meet (phi, psi) -> meet (reduce phi) (reduce psi)
  | Eq (r, s) -> eq r s
  | Var v -> var v

let rec condition : ('v, 'a, 'b) tree -> ('v, 'a) cof =
  function
  | Const (psi, _) -> 
    psi
  | Split (t0, t1) ->
    meet (condition t0) (condition t1)
  | Abort ->
    bot



(* TODO: make the output more beautiful *)
let rec pp_cof pp_v pp env fmt =
  function
  | Eq (x, y) -> 
    Format.fprintf fmt "%a = %a"
      (pp env) x
      (pp env) y
  | Join (phi, psi) ->
    Format.fprintf fmt "(%a) \\/ (%a)"
      (pp_cof pp_v pp env) phi
      (pp_cof pp_v pp env) psi
  | Meet (phi, psi) ->
    Format.fprintf fmt "(%a) /\\ (%a)"
      (pp_cof pp_v pp env) phi
      (pp_cof pp_v pp env) psi
  | Bot -> 
    Format.fprintf fmt "false"
  | Top -> 
    Format.fprintf fmt "true"
  | Var v ->
    pp_v env fmt v


let pp_tree pp_v ppa ppb env fmt = 
  function
  | _ ->
    Format.fprintf fmt "TODO: pp_tree"