module CS := ConcreteSyntax
module D := Domain

type t

val init : t
val bindings : t -> CS.ident list
val check_env : t -> Check.Env.t
val push_name : CS.ident -> t -> t
val push_names : CS.ident list -> t -> t
val find_ix : CS.ident -> t -> int option
val add_term : D.t -> D.tp -> t -> t
val add_top_level : D.t -> D.tp -> t -> t