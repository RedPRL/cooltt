module CS = ConcreteSyntax
module D = Domain
module S = Syntax
module St = ElabState
module Env = ElabEnv
module EM = ElabMonad
module Err = ElabError

open Monad.Notation (EM)

let push_var id tp : 'a m -> 'a m = 
  EM.local @@ fun env ->
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

let quote tp el = 
  let nf = D.Nf {tp; term = el} in
  let* st = EM.get in
  let* env = EM.read in
  match Nbe.read_back_nf st (Env.size env) nf with
  | t -> EM.ret t
  | exception exn -> EM.throw exn

let quote_ne ne = 
  let* st = EM.get in
  let* env = EM.read in
  match Nbe.read_back_ne st (Env.size env) ne with
  | t -> EM.ret t
  | exception exn -> EM.throw exn

let quote_tp tp = 
  let* st = EM.get in
  let* env = EM.read in
  match Nbe.read_back_tp st (Env.size env) tp with
  | tp -> EM.ret tp
  | exception exn -> EM.throw exn



let read_sem_env =
  let+ env = EM.read in
  Env.to_sem_env env

let eval_tp tp =
  let* st = EM.get in
  let* sem_env = read_sem_env in
  match Nbe.eval_tp st sem_env tp with
  | v -> EM.ret v
  | exception exn -> EM.throw exn

let eval_tm tp =
  let* st = EM.get in
  let* sem_env = read_sem_env in
  match Nbe.eval st sem_env tp with
  | v -> EM.ret v
  | exception exn -> EM.throw exn

let inst_tp_clo clo v =
  let* st = EM.get in
  match Nbe.do_tp_clo st clo v with
  | v -> EM.ret v
  | exception exn -> EM.throw exn

let equate tp l r =
  let* st = EM.get in
  let* env = EM.read in
  match
    Nbe.equal_nf st (Env.size env)
      (D.Nf {tp; term = l})
      (D.Nf {tp; term = r})
  with
  | true -> EM.ret ()
  | false -> EM.throw @@ Err.ElabError (Err.ExpectedEqual (tp, l, r))

let equate_tp tp tp' =
  let* st = EM.get in
  let* env = EM.read in
  match Nbe.equal_tp st (Env.size env) tp tp' with
  | true -> EM.ret ()
  | false -> EM.throw @@ Err.ElabError (Err.ExpectedEqualTypes (tp, tp'))

let dest_pi = 
  function
  | D.Pi (base, fam) -> EM.ret (base, fam)
  | tp -> EM.throw @@ Err.ElabError (Err.ExpectedConnective (`Pi, tp))