module Env = ElabEnv
module St = ElabState
module CS = ConcreteSyntax
module D = Domain

type 'a m = St.t * Env.t -> ('a, exn) result * St.t

let read (st, env) = Ok env, st
let get (st, _) = Ok st, st
let set st (_, _) = Ok (), st

let throw exn (st, _) = Error exn, st

let run m env = 
  let res, _ = m (St.init, env) in 
  res

let ret a (st, _) = Ok a, st

let bind (m : 'a m) (k : 'a -> 'b m) : 'b m =
  fun (st, env) ->
  match m (st, env) with
  | Ok a, st' -> k a (st', env)
  | Error exn, st' -> Error exn, st'

let local f m (st, env) = 
  m (st, f env)

let globally m =
  local (fun _ -> Env.init) m

let emit pp a : unit m = 
  fun (st, _env) -> 
  let () = pp Format.std_formatter a in 
  Ok (), st


let lift_qu (m : 'a NbeMonads.quote) : 'a m = 
  fun (st, env) ->
  match NbeMonads.QuM.run (st, Env.size env) m with 
  | Ok v -> Ok v, st
  | Error exn -> Error exn, st

let lift_ev (m : 'a NbeMonads.evaluate) : 'a m = 
  fun (st, env) ->
  match NbeMonads.EvM.run (st, Env.to_sem_env env) m with 
  | Ok v -> Ok v, st 
  | Error exn -> Error exn, st

let lift_cmp (m : 'a NbeMonads.compute) : 'a m = 
  fun (st, _env) ->
  match NbeMonads.CmpM.run st m with
  | Ok v -> Ok v, st 
  | Error exn -> Error exn, st