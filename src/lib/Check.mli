module Env : 
sig
  type entry =
      Term of {term : Domain.t; tp : Domain.tp}
    | TopLevel of {term : Domain.t; tp : Domain.tp}

  type t
  val empty : t
  val size : t -> int
  val add_entry : entry -> t -> t
  val add_term : term:Domain.t -> tp:Domain.tp -> t -> t
  val to_sem_env : t -> Domain.env
  val get_var : t -> int -> Domain.tp
  val get_entry : t -> int -> entry
end 

type env = Env.t

type error
val pp_error : Format.formatter -> error -> unit

exception Type_error of error

val check : env:env -> term:Syntax.t -> tp:Domain.tp -> unit
val synth : env:env -> term:Syntax.t -> Domain.tp
val check_tp : env:env -> tp:Syntax.tp -> unit
