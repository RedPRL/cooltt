type env
val initial_env : env

type output =
    NoOutput of env
  | NF_term of Syntax.t * Domain.t
  | NF_def of Concrete_syntax.ident * Domain.t
  | Quit

val output : env -> output -> unit
val update_env : env -> output -> env

val process_decl : env -> Concrete_syntax.decl -> output
