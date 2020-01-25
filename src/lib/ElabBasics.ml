module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv
module Err = ElabError

open CoolBasis
open Bwd
include Monads.ElabM

open Monad.Notation (Monads.ElabM)

let elab_err err = raise @@ Err.ElabError err


let push_var id tp : 'a m -> 'a m = 
  scope @@ fun env ->
  let con = D.mk_var tp @@ Env.size env in 
  Env.append_con id con tp env

let push_def id tp con : 'a m -> 'a m = 
  scope @@ fun env ->
  Env.append_con id con tp env


let resolve id = 
  let* env = read in
  match Env.resolve_local id env with
  | Some ix -> ret @@ `Local ix
  | None -> 
    let* st = get in
    match St.resolve_global id st with
    | Some sym -> ret @@ `Global sym
    | None -> ret `Unbound

let add_global id tp con = 
  let* st = get in
  let sym, st' = St.add_global id tp con st in
  let* () = set st' in 
  ret sym

let add_flex_global tp = 
  let* st = get in
  let sym, st' = St.add_flex_global tp st in 
  let* () = set st' in 
  ret sym

let get_global sym : (D.tp * D.con) m =
  let* st = get in
  match St.get_global sym st with
  | tp, con -> ret (tp, con)
  | exception exn -> throw exn

let get_local_tp ix =
  let* env = read in
  match Env.get_local_tp ix env with
  | tp -> ret tp
  | exception exn -> throw exn


let get_local ix =
  let* env = read in
  match Env.get_local ix env with
  | tp -> ret tp
  | exception exn -> throw exn

let equate tp l r =
  let* env = read in
  let* res = lift_qu @@ Nbe.equal_con tp l r in
  if res then ret () else 
    let* ttp = lift_qu @@ Nbe.quote_tp tp in
    let* tl = lift_qu @@ Nbe.quote_con tp l in
    let* tr = lift_qu @@ Nbe.quote_con tp r in
    elab_err @@ Err.ExpectedEqual (Env.pp_env env, ttp, tl, tr)

let equate_tp tp tp' =
  let* env = read in
  let* res = lift_qu @@ Nbe.equal_tp tp tp' in 
  if res then ret () else 
    let* ttp = lift_qu @@ Nbe.quote_tp tp in
    let* ttp' = lift_qu @@ Nbe.quote_tp tp' in
    elab_err @@ Err.ExpectedEqualTypes (Env.pp_env env, ttp, ttp')

let dest_pi = 
  function
  | D.Tp (D.Pi (base, fam)) -> 
    ret (base, fam)
  | tp -> 
    elab_err @@ Err.ExpectedConnective (`Pi, tp)

let dest_sg = 
  function
  | D.Tp (D.Sg (base, fam)) -> 
    ret (base, fam)
  | tp -> 
    elab_err @@ Err.ExpectedConnective (`Sg, tp)

let dest_id =
  function
  | D.Tp (D.Id (tp, l, r)) ->
    ret (tp, l, r)
  | tp ->
    elab_err @@ Err.ExpectedConnective (`Id, tp)

let abstract nm tp k =
  push_var nm tp @@
  let* x = get_local 0 in
  k x

let define nm tp con k =
  push_def nm tp con @@
  let* x = get_local 0 in
  k x

let problem = 
  let+ env = read in
  Env.problem env

let push_problem lbl = 
  scope @@ 
  Env.push_problem lbl

let current_ghost : S.ghost option m =
  let* env = read in 
  let rec go_locals = 
    function
    | Emp -> ret []
    | Snoc (cells, `Con cell) ->
      begin
        match Env.ConCell.visibility cell with 
        | `Hidden ->
          go_locals cells
        | `Visible ->
          let* cells = go_locals cells in
          let tp = Env.ConCell.tp cell in
          let* ttp = lift_qu @@ Nbe.quote_tp tp in
          let* tm = lift_qu @@ Nbe.quote_con tp @@ Env.ConCell.con cell in
          ret @@ cells @ [`Con (ttp, tm)]
      end
    | Snoc (cells, `Dim cell) ->
      let* cells = go_locals cells in
      let+ r = lift_qu @@ Nbe.quote_dim @@ Env.DimCell.dim cell in
      cells @ [`Dim r]
  in
  let+ cells = go_locals @@ Env.locals env in
  match Env.problem env with
  | Emp -> None
  | problem -> Some (problem, cells)