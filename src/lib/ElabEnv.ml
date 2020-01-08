module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

open CoolBasis.Bwd
open BwdNotation

type cell = D.nf * string option

type t = 
  {resolver : Symbol.t StringMap.t;
   veil : Veil.t;
   locals : cell bwd}

let locals env = env.locals

let init = 
  {resolver = StringMap.empty;
   veil = Veil.const `Translucent;
   locals = Emp}

let size env = Bwd.length env.locals

let get_local_tp ix env = 
  match Bwd.nth env.locals ix with 
  | D.Nf {tp; _}, _ -> tp

let get_local ix env = 
  match Bwd.nth env.locals ix with 
  | D.Nf {con; _}, _ -> con

let resolve_local key env =
  let exception E in
  let rec go i = function
    | Emp -> raise E
    | Snoc (xs, (_, Some x)) -> if String.equal x key then i else go (i + 1) xs
    | Snoc (xs, (_, None)) -> go (i + 1) xs
  in
  match go 0 @@ env.locals with
  | i -> Some i
  | exception E -> None


let append_el name con tp env =
  {env with 
   locals = env.locals <>< [D.Nf {tp; con}, name]}


let sem_env env : D.env =
  {locals = 
     Bwd.map (function D.Nf {con; _}, _-> con)
       env.locals}

let veil env = env.veil