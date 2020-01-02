module D := Domain
module S := Syntax

type env = ElabEnv.t
type error

val pp_error : Format.formatter -> error -> unit

exception TypeError of error

val check : env:env -> term:S.t -> tp:D.tp -> unit
val synth : env:env -> term:S.t -> D.tp
val check_tp : env:env -> tp:S.tp -> unit