type env

type output =
    NoOutput of env
  | NF_term of Syntax.t * Domain.t
  | NF_def of Concrete_syntax.ident * Domain.t
  | Quit

val output : env -> output -> unit
val update_env : env -> output -> env

val process_sign : ?env:env -> Concrete_syntax.signature -> unit
