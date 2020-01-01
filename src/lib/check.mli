module Env : 
sig
  type entry =
      Term of {term : Domain.t; tp : Domain.t}
    | TopLevel of {term : Domain.t; tp : Domain.t}

  type t
  val empty : t
  val add_entry : entry -> t -> t
  val add_term : term:Domain.t -> tp:Domain.t -> t -> t
  val to_sem_env : t -> Domain.env
  val get_var : t -> int -> Domain.t
  val get_entry : t -> int -> entry
end 

type env = Env.t

type error =
    Cannot_synth_term of Syntax.t
  | Type_mismatch of Domain.t * Domain.t
  | Expecting_universe of Domain.t
  | Misc of string

val pp_error : Format.formatter -> error -> unit

exception Type_error of error

val check : env:env -> term:Syntax.t -> tp:Domain.t -> unit
val synth : env:env -> term:Syntax.t -> Domain.t
val check_tp : env:env -> tp:Syntax.tp -> unit
