open Basis

type env
type symbol = Symbol.t

val empty : env
val resolve : string -> env -> symbol option
val unresolve : symbol -> env -> string option

(** A [native] is an address to a declaration in the {i current} unit. *)
type native = int

val add_native : string option -> symbol -> env -> env

val native_of_symbol : symbol -> env -> native option
