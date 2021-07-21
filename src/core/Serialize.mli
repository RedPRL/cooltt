open CodeUnit

module S = Syntax
module J = Ezjsonm

val serialize_goal : (Ident.t * S.tp) list -> S.tp -> J.t
val deserialize_goal : J.t -> (Ident.t * S.tp) list * S.tp
