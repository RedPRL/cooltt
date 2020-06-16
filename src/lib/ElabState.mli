open Basis

module S := Syntax

type t

val init : t
val add_global : Ident.t -> Decl.t -> t -> Symbol.t * t

val resolve_global : Ident.t -> t -> Symbol.t option

val get_global : Symbol.t -> t -> Decl.t
