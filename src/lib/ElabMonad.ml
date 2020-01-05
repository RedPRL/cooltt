module Env = ElabEnv
module St = ElabState
module CS = ConcreteSyntax
module D = Domain


type 'a result = 
  | Ret of 'a
  | Throw of exn

type 'a m = St.t * Env.t -> 'a result * St.t

let read (st, env) = Ret env, st
let get (st, _) = Ret st, st
let set st (_, _) = Ret (), st

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

let globally m =
  local (fun _ -> Env.init) m

let emit pp a : unit m = 
  fun (st, _env) -> 
  let () = pp Format.std_formatter a in 
  Ret (), st


let lift_qu (m : 'a NbeMonads.quote) : 'a m = 
  fun (st, env) ->
  match NbeMonads.QuM.run m st @@ Env.size env with 
  | v -> Ret v, st
  | exception exn -> Throw exn, st

let lift_ev (m : 'a NbeMonads.evaluate) : 'a m = 
  fun (st, env) ->
  match NbeMonads.EvM.run m st @@ Env.to_sem_env env with 
  | v -> Ret v, st 
  | exception exn -> Throw exn, st

let lift_cmp (m : 'a NbeMonads.compute) : 'a m = 
  fun (st, _env) ->
  match NbeMonads.CmpM.run m st with
  | v -> Ret v, st 
  | exception exn -> Throw exn, st