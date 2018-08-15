type env_entry =
    Term of {term : Domain.t; tp : Domain.t; under_lock : int; is_active : bool}
  | Tick of {under_lock : int; is_active : bool}
type env = env_entry list

exception Type_error
exception Cannot_synth

val check : env:env -> term:Syntax.t -> tp:Syntax.t -> unit
val synth : env:env -> term:Syntax.t -> Domain.t
