open Basis
module Y := Yuujinchou

type env
type pattern = unit Y.Pattern.pattern
type path = Y.Pattern.path

val empty : env
val singleton : path -> Symbol.t -> env

val remap : pattern -> env -> env
val import : ?pattern:pattern -> import:env -> env -> env

val find_opt : path -> env -> Symbol.t option
