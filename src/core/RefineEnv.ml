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
  type 'a t = {
    contents : 'a;
    ident : Ident.t;
    is_dom : bool
  }

  let make nm c dom = {contents = c; ident = nm; is_dom = dom}
  let ident cell = cell.ident
  let contents cell = cell.contents
  let is_dom cell = cell.is_dom
end

type cell = (D.tp * D.con) Cell.t

(* [NOTE: Binding Domain Variables]
   With the addition of fibrant subtypes, we need to track which
   variables are allowed to appear in the cofibration of a fibrant
   subtype. This is to avoid problematic cases like the following:

   > def badCoe (A : type) (x y : A) : path A x y :=
   >  i => coe {j => {fsub A with [ j=0 => x | j=1 => y ]}} 0 i x

   In particular, we need to ensure that the cofibration variables
   are only bound by pi types; this avoids the problematic cases
   with 'coe', as 'j' variable is not bound in this manner.

   However, codes for pi are somewhat problematic, as the actual
   variable binding is handled via a lambda. This means that
   when we elaborate the code for a pi type, we need to flag
   that the *next* variable we bind is a "domain variable"; IE:
   a variable that can show up in an 'fsub' cofibration. This
   is handled by the 'mark_next_dom' field, which is flipped
   when we elaborate a pi type/pi code, and reset once 'append_con'
   is called. *)

type t =
  {
    (* local assumptions *)
    locals : cell bwd;
    cof_thy : CofThy.Disj.t;
    pp : Pp.env;
    mark_next_dom : bool; (* See [NOTE: Binding Domain Variables] *)
    fib_only : bool; (*if only fancy local variables allowed *)
    (* location *)
    location : LexingUtil.span option;
  }

let init =
  { locals = Emp;
    cof_thy = CofThy.Disj.empty;
    pp = Pp.Env.emp;
    mark_next_dom = false;
    fib_only = false;
    location = None }

let globally env =
  { locals = Emp;
    cof_thy = CofThy.Disj.empty;
    pp = Pp.Env.emp;
    mark_next_dom = false;
    fib_only = false;
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
        | `User parts_x, `User parts_y when List.equal String.equal parts_x parts_y ->
          if env.fib_only && not (Cell.is_dom cell) then
            `NotDomain i
          else
            `Local i
        | _ -> go (i + 1) xs
      end
  in
  try go 0 @@ env.locals with
  | E -> `NotFound

let dump_local fmt (cell : cell) =
  let (tp , con) = cell.contents in
  Format.fprintf fmt "(%b) %a : %a := @[<hov 2>%a@]" cell.is_dom Ident.pp cell.ident D.pp_tp tp D.pp_con con

let dump_locals fmt : cell list -> unit =
  Format.pp_print_list ~pp_sep:Format.pp_print_newline dump_local fmt

let mark_next_dom b env = { env with mark_next_dom = b }

let is_fib_only env = env.fib_only

let fib_only env = {env with fib_only = true}

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
   locals = env.locals #< (Cell.make ident (tp, con) env.mark_next_dom);
   mark_next_dom = false; (* See [NOTE: Binding Domain Variables] *)
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
