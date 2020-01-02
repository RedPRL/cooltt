module Env = ElabEnv 
module CS = ConcreteSyntax
module D = Domain

type 'a m = Env.t -> [`Ret of 'a | `Throw of exn]

let read env = `Ret env
let throw exn _env = `Throw exn
let run m env = m env

let ret a _env = `Ret a
let bind m k = 
  fun env ->
  match m env with 
  | `Ret a ->
    k a env
  | `Throw exn ->
    `Throw exn

let push_var id tp m = 
  fun env ->
  let var = D.Var (Check.Env.size @@ Env.check_env env) in
  let term = D.Neutral {term = var; tp} in 
  let entry = Check.Env.Term {term; tp} in
  let env' = Env.add_entry entry @@ Env.push_name id env in 
  m env'
