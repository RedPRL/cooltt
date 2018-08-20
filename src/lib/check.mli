type env_entry =
    Term of {term : Domain.t; tp : Domain.t; locks : int; is_active : bool}
  | Tick of {locks : int; is_active : bool}
type env = env_entry list

exception Type_error
exception Cannot_use_var
exception Cannot_synth of Syntax.t

val check : env:env -> size:int -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:env -> size:int -> term:Syntax.t -> Domain.t
