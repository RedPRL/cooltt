open ContainersLabels
open Basis
open Bwd
open BwdNotation

open CodeUnit

module StringMap = Map.Make (String)
module D = Domain
module S = Syntax

module IntSet = Set.Make (Int)

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
  {
    (* local assumptions *)
    locals : cell bwd;
    cof_thy : CofThy.Disj.t;
    pp : Pp.env;
    fib_vars : IntSet.t; (* fancy vars *)
    is_fib : bool; (* if ussing fib_vars *)

    (* location *)
    location : LexingUtil.span option;
  }

let init =
  { locals = Emp;
    cof_thy = CofThy.Disj.empty;
    pp = Pp.Env.emp;
    fib_vars = IntSet.empty;
    is_fib = false;
    location = None }

let globally env =
  { locals = Emp;
    cof_thy = CofThy.Disj.empty;
    pp = Pp.Env.emp;
    fib_vars = IntSet.empty;
    is_fib = false;
    location = env.location }


(* local assumptions *)
let locals env = env.locals
let size env = BwdLabels.length env.locals
let get_local_tp ix env =
  let cell = BwdLabels.nth env.locals ix in
  let tp, _ = Cell.contents cell in
  tp
let get_local ix env =
  let cell = BwdLabels.nth env.locals ix in
  let _, con = Cell.contents cell in
  con
let resolve_local (ident : Ident.t) env =
  let exception E in
  let rec go i = function
    | Emp -> raise E
    | Snoc (xs, cell) ->
      begin
        match ident, Cell.ident cell with
        | `User parts_x, `User parts_y when List.equal String.equal parts_x parts_y -> i
        | _ -> go (i + 1) xs
      end
  in
  match go 0 @@ env.locals with
  | i -> Some i
  | exception E -> None
let rec dump_locals fmt : (D.tp * D.con) Cell.t list -> unit =
  function
  | [] -> ()
  | (cell :: cells) ->
    Format.fprintf fmt "%a : %a := @[<hov 2>%a@]@;%a" Ident.pp cell.ident D.pp_tp (fst cell.contents) D.pp_con (snd cell.contents) dump_locals cells

(*
let is_fib_var lvl env =
  if env.is_fib
    then IntSet.mem lvl env.fib_vars
    else true
*)
let set_fib b env = {env with is_fib = b}

let is_fib env = env.is_fib

let add_fib_var lvl env = {env with fib_vars = IntSet.add lvl env.fib_vars}

let get_fib_vars env =
  Bwd.of_list @@ List.map (BwdLabels.nth env.locals) (IntSet.to_list env.fib_vars)

let fib_only env = {env with locals = get_fib_vars env}

(* cofibrations and others *)
let local_cof_thy env = env.cof_thy
let pp_env env = env.pp
let sem_env (env : t) : D.env =
  {tpenv = Emp;
   conenv =
     BwdLabels.map env.locals
       ~f:(fun cell ->
           let _, con = Cell.contents cell in
           con)}
let restrict phis env =
  {env with
   cof_thy = CofThy.Disj.assume env.cof_thy phis}
let append_con ident con tp env =
  {env with
   pp = snd @@ Pp.Env.bind env.pp (Ident.to_string_opt ident);
   locals = env.locals #< (Cell.make ident (tp, con));
   cof_thy =
     match tp with
     | D.TpPrf phi -> CofThy.Disj.assume env.cof_thy [phi]
     | _ -> env.cof_thy}

(* locations *)
let location env = env.location
let set_location loc env =
  match loc with
  | Some _ -> {env with location = loc}
  | _ -> env

let dump fmt : t -> unit =
  fun env ->
  Format.fprintf fmt "Locals: @[<v>%a@]" dump_locals (BwdLabels.to_list env.locals)
