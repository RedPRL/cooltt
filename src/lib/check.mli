type env_entry =
    Term of {term : Domain.t; tp : Domain.t; locks : int; is_active : bool}
  | TopLevel of {term : Domain.t; tp : Domain.t}
  | Tick of {locks : int; is_active : bool}
type env = env_entry list

val env_to_sem_env : int -> env -> Domain.env

type error =
    Cannot_synth_term of Syntax.t
  | Using_killed_tick
  | Using_killed_variable
  | Using_locked_tick
  | Using_locked_variable
  | Using_non_tick
  | Using_non_term
  | Type_mismatch of Domain.t * Domain.t
  | Expecting_universe of Domain.t
  | Misc of string

val pp_error : error -> string

exception Type_error of error

val check : env:env -> size:int -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:env -> size:int -> term:Syntax.t -> Domain.t
val check_tp : env:env -> size:int -> term:Syntax.t -> unit
