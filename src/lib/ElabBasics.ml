module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv
module EM = ElabMonad
module Err = ElabError

open Monad.Notation (EM)

let push_var id tp : 'a m -> 'a m = 
  EM.scope @@ fun env ->
  let var = D.Var (Env.size env) in
  let term = D.Ne {ne = var; tp} in
  Env.push_term id term tp env

let resolve id = 
  let* env = EM.read in
  match Env.resolve_local id env with
  | Some ix -> EM.ret @@ `Local ix
  | None -> 
    let* st = EM.get in
    match St.resolve_global id st with
    | Some sym -> EM.ret @@ `Global sym
    | None -> EM.ret `Unbound

let add_global id tp el = 
  let* st = EM.get in
  let sym, st' = St.add_global id tp el st in
  let* () = EM.set st' in 
  EM.ret sym

let get_global sym : D.nf m =
  let* st = EM.get in
  match St.get_global sym st with
  | nf -> EM.ret nf
  | exception exn -> EM.throw exn

let get_local_tp ix =
  let* env = EM.read in
  match Env.get_local_tp ix env with
  | tp -> EM.ret tp
  | exception exn -> EM.throw exn


let get_local ix =
  let* env = EM.read in
  match Env.get_local ix env with
  | tp -> EM.ret tp
  | exception exn -> EM.throw exn

let equate tp l r =
  let* res = EM.lift_qu @@ Nbe.Monadic.equal tp l r in
  if res then EM.ret () else 
    EM.throw @@ Err.ElabError (Err.ExpectedEqual (tp, l, r))

let equate_tp tp tp' =
  let* res = EM.lift_qu @@ Nbe.Monadic.equal_tp tp tp' in 
  if res then EM.ret () else 
    EM.throw @@ Err.ElabError (Err.ExpectedEqualTypes (tp, tp'))

let dest_pi = 
  function
  | D.Pi (base, fam) -> EM.ret (base, fam)
  | tp -> EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Pi, tp))