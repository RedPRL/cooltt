module CS := ConcreteSyntax
module D := Domain

type t

val init : t
val push_term : string option -> D.t -> D.tp -> t -> t
val add_top_level : string -> D.t -> D.tp -> t -> t
val to_sem_env : t -> D.env

val size : t -> int

(* TODO: make return option *)
val get_global : Symbol.t -> t -> D.nf
val get_local : int -> t -> D.tp

val resolve : CS.ident -> t -> [`Local of int | `Global of Symbol.t | `Unbound]