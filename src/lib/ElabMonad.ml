module Env = ElabEnv
module CS = ConcreteSyntax
module D = Domain


type 'a result = 
  | Ret of 'a
  | Throw of exn

type 'a m = Env.t -> 'a result

let read env = Ret env

let throw exn _env = Throw exn

let run m env = m env

let ret a _env = Ret a

let bind m k env =
  match m env with
  | Ret a -> k a env
  | Throw exn -> Throw exn

let push_var id tp (m : 'a m) : 'a m = 
  fun env ->
  let var = D.Var (Env.size env) in
  let term = D.Neutral {term = var; tp} in
  let env' = Env.push_term (Some id) term tp env in
  m env'