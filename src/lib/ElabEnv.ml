module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

type cell = D.nf * string option

type t = 
  {resolver : Symbol.t StringMap.t;
   locals : cell list}

let locals env = env.locals

let init = 
  {resolver = StringMap.empty;
   locals = []}

let size env = List.length env.locals

let get_local ix env = 
  match List.nth env.locals ix with 
  | D.Nf {tp; _}, _ -> tp

let resolve_local key env =
  let exception E in
  let rec go i = function
    | [] -> raise E
    | (_, Some x) :: xs -> if String.equal x key then i else go (i + 1) xs
    | (_, None) :: xs -> go (i + 1) xs
  in
  match go 0 @@ env.locals with
  | i -> Some i
  | exception E -> None


let push_term name term tp env =
  {env with 
   locals = (D.Nf {tp; term}, name) :: env.locals}


let to_sem_env env : D.env =
  {locals = 
     List.map (function D.Nf {term; _}, _-> term)
       env.locals}