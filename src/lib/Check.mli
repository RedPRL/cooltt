module D := Domain
module S := Syntax

type state = ElabState.t
type env = ElabEnv.t
type error

val pp_error : Format.formatter -> error -> unit

exception TypeError of error

val check : st:state -> env:env -> term:S.t -> tp:D.tp -> unit
val synth : st:state -> env:env -> term:S.t -> D.tp
val check_tp : st:state -> env:env -> tp:S.tp -> unit