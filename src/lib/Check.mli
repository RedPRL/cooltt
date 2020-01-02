module D := Domain
module S := Syntax

module Env : sig
  type entry =
    | Term of {term : D.t; tp : D.tp}
    | TopLevel of {term : D.t; tp : D.tp}

  type t

  val empty : t
  val size : t -> int
  val add_entry : entry -> t -> t
  val add_term : term:D.t -> tp:D.tp -> t -> t
  val to_sem_env : t -> D.env
  val get_var : t -> int -> D.tp
  val get_entry : t -> int -> entry
end

type env = Env.t
type error

val pp_error : Format.formatter -> error -> unit

exception TypeError of error

val check : env:env -> term:S.t -> tp:D.tp -> unit
val synth : env:env -> term:S.t -> D.tp
val check_tp : env:env -> tp:S.tp -> unit
