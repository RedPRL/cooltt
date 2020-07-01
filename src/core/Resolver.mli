open Basis

type env
type symbol = Symbol.t

type attr = [`Public | `Private]

val empty : env
val resolve : string -> env -> symbol option
val unresolve : symbol -> env -> string option

(** A [native] is an address to a declaration in the {i current} unit. *)
type native = int

val add_native : attr:attr -> string option -> symbol -> env -> env

val native_of_symbol : symbol -> env -> native option
val symbol_of_native : native -> env -> symbol option
