module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

open CoolBasis
open Bwd
open BwdNotation

module Cell =
struct
  type 'a t = 
    {contents : 'a;
     name : string option}

  let make nm c = {contents = c; name = nm}
  let name cell = cell.name
  let contents cell = cell.contents
end

type cell = 
  [ `Con of (D.tp * D.con) Cell.t
  | `Dim of D.dim Cell.t
  | `Cof of D.cof Cell.t
  | `Prf of D.cof
  ]

type t = 
  {resolver : Symbol.t StringMap.t;
   veil : Veil.t;
   pp : Pp.env;
   cof_env : CofEnv.env;
   locals : cell bwd;
   problem : string bwd}

let locals env = env.locals

let init = 
  {resolver = StringMap.empty;
   veil = Veil.const `Translucent;
   pp = Pp.Env.emp;
   cof_env = CofEnv.init ();
   locals = Emp;
   problem = Emp}

let size env = Bwd.length env.locals

let get_local_tp ix env = 
  match Bwd.nth env.locals ix with
  | `Con cell -> 
    let tp, _ = Cell.contents cell in 
    tp
  | _ -> 
    failwith "get_local_tp"

let get_local ix env = 
  match Bwd.nth env.locals ix with
  | `Con cell -> 
    let _, con = Cell.contents cell in
    con
  | _ -> 
    failwith "get_local"

let resolve_local key env =
  let exception E in
  let rec go i = function
    | Emp -> raise E
    | Snoc (xs, `Con cell) ->
      begin
        match Cell.name cell with
        | Some x when x = key -> i
        | _ -> go (i + 1) xs
      end
    | Snoc (xs, `Dim cell) ->
      begin
        match Cell.name cell with
        | Some x when x = key -> i
        | _ -> go (i + 1) xs
      end
    | Snoc (xs, `Cof cell) ->
      begin
        match Cell.name cell with
        | Some x when x = key -> i
        | _ -> go (i + 1) xs
      end
    | Snoc (xs, `Prf _) ->
      go i xs
  in
  match go 0 @@ env.locals with
  | i -> Some i
  | exception E -> None


let append_con name con tp env =
  {env with 
   pp = snd @@ Pp.Env.bind env.pp name;
   locals = env.locals <>< [`Con {contents = tp, con; name}]}

let append_dim name r env = 
  {env with 
   pp = snd @@ Pp.Env.bind env.pp name;
   locals = env.locals <>< [`Dim {contents = r; name}]}


let append_prf phi env = 
  {env with 
   locals = env.locals <>< [`Prf phi];
   cof_env = CofEnv.assume env.cof_env phi}


let sem_env (env : t) : D.env =
  env.locals |> Bwd.filter_map @@ function 
  | `Con cell ->
    let _, con = Cell.contents cell in
    Some (`Con con)
  | `Dim cell ->
    Some (`Dim (Cell.contents cell))
  | `Cof cell -> 
    Some (`Cof (Cell.contents cell))
  | `Prf _ ->
    None

let pp_env env = env.pp

let cof_env env = env.cof_env

let get_veil env = env.veil
let set_veil v env = {env with veil = v}

let problem env = env.problem

let push_problem lbl env = 
  {env with
   problem = env.problem #< lbl}