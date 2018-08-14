exception Nbe_failed of string

val normalize : env:Syntax.env -> term:Syntax.t -> tp:Syntax.t -> Syntax.t
val initial_env : Syntax.env -> Domain.env
val eval : Syntax.t -> Domain.env -> Domain.t
val read_back_nf : int -> Domain.nf -> Syntax.t
val read_back_tp : int -> Domain.t -> Syntax.t
val read_back_ne : int -> Domain.ne -> Syntax.t
