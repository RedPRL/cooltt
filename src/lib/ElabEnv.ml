module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

open Bwd
open BwdNotation

type cell = D.nf * string option

type t = 
  {resolver : Symbol.t StringMap.t;
   locals : cell bwd}

let locals env = env.locals

let init = 
  {resolver = StringMap.empty;
   locals = Emp}

let size env = Bwd.length env.locals

let get_local_tp ix env = 
  match Bwd.nth env.locals ix with 
  | D.Nf {tp; _}, _ -> tp

let get_local ix env = 
  match Bwd.nth env.locals ix with 
  | D.Nf {el; _}, _ -> el

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


let push_term name el tp env =
  {env with 
   locals = env.locals <>< [D.Nf {tp; el}, name]}


let to_sem_env env : D.env =
  {locals = 
     Bwd.map (function D.Nf {el; _}, _-> el)
       env.locals}