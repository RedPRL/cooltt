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

type cell = (D.tp * D.con) Cell.t

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
  let cell = Bwd.nth env.locals ix in
  let tp, _ = Cell.contents cell in 
  tp

let get_local ix env = 
  let cell = Bwd.nth env.locals ix in
  let _, con = Cell.contents cell in
  con

let resolve_local key env =
  let exception E in
  let rec go i = function
    | Emp -> raise E
    | Snoc (xs, cell) ->
      begin
        match Cell.name cell with
        | Some x when x = key -> i
        | _ -> go (i + 1) xs
      end
  in
  match go 0 @@ env.locals with
  | i -> Some i
  | exception E -> None


let append_con name con tp env =
  {env with 
   pp = snd @@ Pp.Env.bind env.pp name;
   locals = env.locals <>< [{contents = tp, con; name}];
   cof_env =
     match tp with 
     | D.TpPrf phi -> CofEnv.assume env.cof_env phi
     | _ -> env.cof_env
  }

let sem_env (env : t) : D.env =
  env.locals |> Bwd.filter_map @@ fun cell ->
  let _, con = Cell.contents cell in
  Some con

let pp_env env = env.pp

let cof_env env = env.cof_env

let get_veil env = env.veil
let set_veil v env = {env with veil = v}

let problem env = env.problem

let push_problem lbl env = 
  {env with
   problem = env.problem #< lbl}