type t

val nonassoc : int -> t
val left : int -> t
val right : int -> t
val prefix : int -> t
val postfix : int -> t
val dual : t -> t -> t

type env
val left_of : t -> env
val right_of : t -> env
val surrounded_by : t -> env
val isolated : env
val isolate_right : env -> env
val isolate_left : env -> env

val parens : env -> t -> bool

val pp : Format.formatter -> t -> unit
val pp_env : Format.formatter -> env -> unit
