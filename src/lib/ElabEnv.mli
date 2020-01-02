module CS := ConcreteSyntax

type t

val init : t
val bindings : t -> CS.ident list
val check_env : t -> Check.Env.t
val push_name : CS.ident -> t -> t
val push_names : CS.ident list -> t -> t
val find_ix : CS.ident -> t -> int option
val add_entry : Check.Env.entry -> t -> t
