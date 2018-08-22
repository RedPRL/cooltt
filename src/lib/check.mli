type env_entry =
    Term of {term : Domain.t; tp : Domain.t; locks : int; is_active : bool}
  | Tick of {locks : int; is_active : bool}
type env = env_entry list

type error =
    Cannot_synth_term of Syntax.t
  | Using_killed_tick
  | Using_killed_variable
  | Using_locked_tick
  | Using_locked_variable
  | Using_non_tick
  | Using_non_term
  | Type_mismatch of Syntax.t * Syntax.t
  | Expecting_universe of Domain.t
  | Misc of string

val pp_error : error -> string

exception Type_error of error

val check : env:env -> size:int -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:env -> size:int -> term:Syntax.t -> Domain.t
