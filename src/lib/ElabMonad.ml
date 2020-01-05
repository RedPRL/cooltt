module Env = ElabEnv
module St = ElabState
module CS = ConcreteSyntax
module D = Domain

module M = Monad.MonadReaderStateResult (struct type global = St.t type local = Env.t end)
include M

let globally m =
  m |> scope @@ fun _ -> Env.init

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