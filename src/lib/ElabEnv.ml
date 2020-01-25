module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

open CoolBasis
open Bwd
open BwdNotation


module ConCell : sig 
  type t 
  val make : D.tp -> D.con -> string option -> t
  val tp : t -> D.tp
  val con : t -> D.con
  val name : t -> string option
  val visibility : t -> [`Visible | `Hidden]
end =
struct
  type t = D.tp * D.con * string option
  let make tp con nm = tp, con, nm
  let tp (tp, _, _) = tp 
  let name (_, _, name) = name 
  let con (_, con, _) = con

  let visibility : t -> [`Visible | `Hidden] =
    function
    | (_, _, None) -> `Hidden 
    | _ -> `Visible
end

module DimCell : sig 
  type t
  val make : D.dim -> string option -> t
  val dim : t -> D.dim
  val name : t -> string option
end =
struct
  type t = D.dim * string option
  let make r nm = r, nm
  let dim (r, _) = r 
  let name (_, nm) = nm
end

type cell = [`Con of ConCell.t | `Dim of DimCell.t]

type t = 
  {resolver : Symbol.t StringMap.t;
   veil : Veil.t;
   pp : Pp.env;
   restriction : Restriction.t;
   locals : cell bwd;
   problem : string bwd}

let locals env = env.locals

let init = 
  {resolver = StringMap.empty;
   veil = Veil.const `Translucent;
   pp = Pp.Env.emp;
   restriction = Restriction.emp ();
   locals = Emp;
   problem = Emp}

let size env = Bwd.length env.locals

let get_local_tp ix env = 
  match Bwd.nth env.locals ix with
  | `Con cell -> ConCell.tp cell
  | _ -> 
    failwith "get_local_tp"

let get_local ix env = 
  match Bwd.nth env.locals ix with
  | `Con cell -> ConCell.con cell
  | _ -> 
    failwith "get_local"

let resolve_local key env =
  let exception E in
  let rec go i = function
    | Emp -> raise E
    | Snoc (xs, `Con cell) ->
      begin
        match ConCell.name cell with
        | Some x when x = key -> i
        | _ -> go (i + 1) xs
      end
    | Snoc (xs, `Dim cell) ->
      begin
        match DimCell.name cell with
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
   locals = env.locals <>< [`Con (ConCell.make tp con name)]}


let sem_env (env : t) : D.env =
  env.locals |> Bwd.map @@ function 
  | `Con cell ->
    `Con (ConCell.con cell)
  | `Dim cell ->
    `Dim (DimCell.dim cell)

let pp_env env = env.pp

let restriction env = env.restriction

let get_veil env = env.veil
let set_veil v env = {env with veil = v}

let problem env = env.problem

let push_problem lbl env = 
  {env with
   problem = env.problem #< lbl}