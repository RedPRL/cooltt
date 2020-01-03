module Env = ElabEnv
module St = ElabState
module CS = ConcreteSyntax
module D = Domain


type 'a result = 
  | Ret of 'a
  | Throw of exn

module Base = 
struct
  type 'a m = St.t * Env.t -> 'a result * St.t

  let read (st, env) = Ret env, st
  let get (st, _) = Ret st, st

  let throw exn (st, _) = Throw exn, st

  let run m env = 
    let res, _ = m (St.init, env) in 
    res

  let ret a (st, _) = Ret a, st

  let bind (m : 'a m) (k : 'a -> 'b m) : 'b m =
    fun (st, env) ->
    match m (st, env) with
    | Ret a, st' -> k a (st', env)
    | Throw exn, st' -> Throw exn, st'

  let local f m (st, env) = 
    m (st, f env)
end

include Base
open Monad.Notation (Base)

let push_var id tp : 'a m -> 'a m = 
  local @@ fun env ->
  let var = D.Var (Env.size env) in
  let term = D.Neutral {term = var; tp} in
  Env.push_term (Some id) term tp env

let resolve id = 
  let* env = read in
  match Env.resolve_local id env with
  | Some ix -> ret @@ `Local ix
  | None -> 
    let* st = get in
    match St.resolve_global id st with
    | Some sym -> ret @@ `Global sym
    | None -> ret `Unbound

let add_global id tp el (st, _env) = 
  let st' = St.add_global id tp el st in
  Ret (), st'

let get_global sym : D.nf m =
  let* st = get in
  match St.get_global sym st with
  | nf -> ret nf
  | exception exn -> throw exn

let get_local ix =
  let* env = read in
  match Env.get_local ix env with
  | tp -> ret tp
  | exception exn -> throw exn

let quote nf = 
  let* st = get in
  let* env = read in
  match Nbe.read_back_nf st (Env.size env) nf with
  | t -> ret t
  | exception exn -> throw exn

let emit pp a : unit m = 
  fun (st, _env) -> 
  let () = pp Format.std_formatter a in 
  Ret (), st