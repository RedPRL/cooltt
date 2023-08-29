type path = Yuujinchou.Trie.path

type t
type pattern = [`Print of string option ] Yuujinchou.Language.t
type ('a, 'error) result = ('a, [> `BindingNotFound of path | `Shadowing of path ] as 'error) Stdlib.result

val empty : t

val prefix : path -> t -> t

val transform : shadowing:bool
  -> pp:(Format.formatter -> CodeUnit.Global.t -> unit)
  -> pattern
  -> t
  -> (t, 'error) result

val union : shadowing:bool -> t -> t -> (t, 'error) result

val add : shadowing:bool -> Ident.t -> CodeUnit.Global.t -> t -> (t, 'error) result

val find : Ident.t -> t -> CodeUnit.Global.t option
