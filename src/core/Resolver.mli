open Basis
module Y := Yuujinchou

type env
type pattern = unit Y.Pattern.pattern
type path = Y.Pattern.path
type symbol = Symbol.t

val empty : env
val singleton : path -> symbol -> env

val remap : pattern -> env -> env
val import : ?pattern:pattern -> import:env -> env -> env

val resolve : path -> env -> symbol option
