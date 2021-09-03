open CodeUnit

module S = Syntax
module D = Domain
module J = Ezjsonm

val serialize_goal : (Ident.t * S.tp) list -> S.tp -> J.t
val deserialize_goal : J.t -> (Ident.t * S.tp) list * S.tp

val serialize_bindings : (Ident.t * D.tp * D.con option) list -> J.t
val deserialize_bindings : J.t -> (Ident.t * D.tp * D.con option) list
