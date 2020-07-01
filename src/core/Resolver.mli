open Basis
module Y := Yuujinchou

module Attr :
sig
  type t
  val default : t
  val join : t -> t -> t
  val meet : t -> t -> t
end

type env
type attr = Attr.t
type pattern = attr Y.Pattern.pattern
type path = Y.Pattern.path
type symbol = Symbol.t

module PathSet : Set.S with type elt = path

val empty : env
val singleton : path -> symbol -> attr -> env
val resolve : path -> env -> (symbol * attr) option
val unresolve : symbol -> env -> PathSet.t


exception InconsistentMapping of path * symbol * symbol

val remap : pattern -> env -> env
val import : ?pattern:pattern -> import:env -> env -> env
