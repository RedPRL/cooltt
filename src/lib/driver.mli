type env
type output =
    NoOutput of env
  | NF of Domain.t
  | Quit

val output : output -> unit
val update_env : env -> output -> env

val process_decl : env -> Concrete_syntax.decl -> output
