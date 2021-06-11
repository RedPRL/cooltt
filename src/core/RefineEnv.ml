open Basis
open Cubical
open Bwd
open BwdNotation

open CodeUnit

module StringMap = Map.Make (String)
module D = Domain
module S = Syntax


module Cell =
struct
  type 'a t =
    {contents : 'a;
     ident : Ident.t}

  let make nm c = {contents = c; ident = nm}
  let ident cell = cell.ident
  let contents cell = cell.contents
end

type cell = (D.tp * D.con) Cell.t

type t =
  {resolver : Global.t StringMap.t;
   veil : Veil.t;
   pp : Pp.env;
   cof_thy : CofThy.Disj.t;
   locals : cell bwd;
   problem : string bwd;
   location : LexingUtil.span option}

let locals env = env.locals

let init =
  {resolver = StringMap.empty;
   veil = Veil.const `Translucent;
   pp = Pp.Env.emp;
   cof_thy = CofThy.Disj.empty;
   locals = Emp;
   problem = Emp;
   location = None}

let location env = env.location
let set_location loc env =
  match loc with
  | Some _ -> {env with location = loc}
  | _ -> env

let size env = Bwd.length env.locals

let get_local_tp ix env =
  let cell = Bwd.nth env.locals ix in
  let tp, _ = Cell.contents cell in
  tp

let get_local ix env =
  let cell = Bwd.nth env.locals ix in
  let _, con = Cell.contents cell in
  con

let resolve_local (ident : Ident.t) env =
  let exception E in
  let rec go i = function
    | Emp -> raise E
    | Snoc (xs, cell) ->
      begin
        match ident, Cell.ident cell with
        | `User (parts_x, x), `User (parts_y, y) when x = y && List.for_all2 (=) parts_x parts_y -> i
        | _ -> go (i + 1) xs
      end
  in
  match go 0 @@ env.locals with
  | i -> Some i
  | exception E -> None

let restrict phis env =
  {env with
   cof_thy = CofThy.Disj.assume env.cof_thy phis}

let append_con ident con tp env =
  {env with
   pp = snd @@ Pp.Env.bind env.pp (Ident.to_string_opt ident);
   locals = env.locals <>< [{contents = tp, con; ident}];
   cof_thy =
     match tp with
     | D.TpPrf phi -> CofThy.Disj.assume env.cof_thy [phi]
     | _ -> env.cof_thy}

let sem_env (env : t) : D.env =
  {tpenv = Emp;
   conenv =
     env.locals |> Bwd.map @@ fun cell ->
     let _, con = Cell.contents cell in
     con}

let pp_env env = env.pp

let cof_thy env = env.cof_thy

let get_veil env = env.veil
let set_veil v env = {env with veil = v}

let problem env = env.problem

let push_problem lbl env =
  {env with
   problem = env.problem #< lbl}
