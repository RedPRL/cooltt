module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

open CoolBasis
open Bwd
open BwdNotation


module Cell : sig 
  type t 
  val make : D.tp -> D.con -> string option -> t
  val tp : t -> D.tp
  val con : t -> D.con
  val name : t -> string option
end =
struct
  type t = D.tp * D.con * string option
  let make tp con nm = tp, con, nm
  let tp (tp, _, _) = tp 
  let name (_, _, name) = name 
  let con (_, con, _) = con
end

type cell = Cell.t

type t = 
  {resolver : Symbol.t StringMap.t;
   veil : Veil.t;
   pp : Pp.env;
   locals : cell bwd}

let locals env = env.locals

let init = 
  {resolver = StringMap.empty;
   veil = Veil.const `Translucent;
   pp = Pp.Env.emp;
   locals = Emp}

let size env = Bwd.length env.locals

let get_local_tp ix env = 
  Cell.tp @@ Bwd.nth env.locals ix

let get_local ix env = 
  Cell.con @@ Bwd.nth env.locals ix

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


let append_el name con tp env =
  {env with 
   pp = snd @@ Pp.Env.bind env.pp name;
   locals = env.locals <>< [Cell.make tp con name]}


let sem_env (env : t) : D.env =
  env.locals |> Bwd.map @@ fun cell ->
  `Con (Cell.con cell)

let pp_env env = env.pp

let get_veil env = env.veil

let veil v env = {env with veil = v}