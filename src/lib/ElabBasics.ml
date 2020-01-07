module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv
module Err = ElabError

open CoolBasis
include Monads.ElabM

open Monad.Notation (Monads.ElabM)

let elab_err err = raise @@ Err.ElabError err


let push_var id tp : 'a m -> 'a m = 
  scope @@ fun env ->
  let var = D.Var (Env.size env) in
  let term = D.Ne {cut = var, []; tp} in
  Env.append_el id term tp env

let push_def id tp el : 'a m -> 'a m = 
  scope @@ fun env ->
  Env.append_el id el tp env


let resolve id = 
  let* env = read in
  match Env.resolve_local id env with
  | Some ix -> ret @@ `Local ix
  | None -> 
    let* st = get in
    match St.resolve_global id st with
    | Some sym -> ret @@ `Global sym
    | None -> ret `Unbound

let add_global id tp el = 
  let* st = get in
  let sym, st' = St.add_global id tp el st in
  let* () = set st' in 
  ret sym

let get_global sym : D.nf m =
  let* st = get in
  match St.get_global sym st with
  | nf -> ret nf
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
  let* res = lift_qu @@ Nbe.equal tp l r in
  if res then ret () else 
    elab_err @@ Err.ExpectedEqual (tp, l, r)

let equate_tp tp tp' =
  let* res = lift_qu @@ Nbe.equal_tp tp tp' in 
  if res then ret () else 
    elab_err @@ Err.ExpectedEqualTypes (tp, tp')

let dest_pi = 
  function
  | D.Pi (base, fam) -> 
    ret (base, fam)
  | tp -> 
    elab_err @@ Err.ExpectedConnective (`Pi, tp)

let dest_sg = 
  function
  | D.Sg (base, fam) -> 
    ret (base, fam)
  | tp -> 
    elab_err @@ Err.ExpectedConnective (`Sg, tp)

let dest_id =
  function
  | D.Id (tp, l, r) ->
    ret (tp, l, r)
  | tp ->
    elab_err @@ Err.ExpectedConnective (`Id, tp)