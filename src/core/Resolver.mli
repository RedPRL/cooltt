open Basis
module Y := Yuujinchou

type env
type pattern = unit Y.Pattern.pattern
type path = Y.Pattern.path
type symbol = Symbol.t

module PathSet : Set.S with type elt = path

val empty : env
val singleton : path -> symbol -> env
val resolve : path -> env -> symbol option
val unresolve : symbol -> env -> PathSet.t


exception InconsistentMapping of path * symbol * symbol

val remap : pattern -> env -> env
val import : ?pattern:pattern -> import:env -> env -> env
