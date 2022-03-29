open ContainersLabels
open Basis
open Cubical
open Bwd
open Bwd.Notation

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
  {
    (* declaration-wide *)
    veil : Veil.t;

    (* local assumptions *)
    locals : cell bwd;
    cof_thy : CofThy.Disj.t;
    pp : Pp.env;

    (* location *)
    location : LexingUtil.span option;
  }

let init =
  { veil = Veil.const `Translucent;
    locals = Emp;
    cof_thy = CofThy.Disj.empty;
    pp = Pp.Env.emp;
    location = None }

let globally env =
  { veil = env.veil;
    locals = Emp;
    cof_thy = CofThy.Disj.empty;
    pp = Pp.Env.emp;
    location = env.location }

(* veil *)
let get_veil env = env.veil
let set_veil v env = {env with veil = v}

(* local assumptions *)
let locals env = env.locals
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

(* cofibrations and others *)
let local_cof_thy env = env.cof_thy
let pp_env env = env.pp
let sem_env (env : t) : D.env =
  {tpenv = Emp;
   conenv =
     env.locals |>
     Bwd.map ~f:(fun cell ->
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
  Format.fprintf fmt "Locals: @[<v>%a@]" dump_locals (Bwd.to_list env.locals)
