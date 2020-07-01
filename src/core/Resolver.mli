open Basis
module Y := Yuujinchou

type env
type symbol = Symbol.t

val empty : env
val resolve : string -> env -> symbol option
val unresolve : symbol -> env -> string option

val add_native : string option -> symbol -> env -> env
