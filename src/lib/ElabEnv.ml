module StringMap = Map.Make (String)
module D = Domain

type t = 
  {globals : D.nf SymbolMap.t;
   resolver : Symbol.t StringMap.t;
   locals : (D.nf * string option) list}

let init = 
  {globals = SymbolMap.empty;
   resolver = StringMap.empty;
   locals = []}

let size env = List.length env.locals

let get_global sym env = 
  SymbolMap.find sym env.globals

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

let resolve_global key env = 
  StringMap.find_opt key env.resolver

let resolve key env = 
  match resolve_local key env with
  | Some ix -> `Local ix
  | None ->
    match resolve_global key env with 
    | Some sym -> `Global sym
    | None -> `Unbound


let add_top_level name term tp env =
  let sym = Symbol.named name in
  {env with 
   resolver = StringMap.add name sym env.resolver;
   globals = SymbolMap.add sym (D.Nf {term; tp}) env.globals}


let push_term name term tp env =
  {env with 
   locals = (D.Nf {tp; term}, name) :: env.locals}


let to_sem_env env : D.env =
  {globals = env.globals;
   locals = 
     List.map (function D.Nf {term; _}, _-> term)
       env.locals}