(* This is the top-level driver for the proof assistant. *)

val find_project_root : [`Stdin | `File of string] -> string

val load_file : string -> [`Stdin | `File of string] -> (unit, unit) result
val do_repl : string -> (unit, unit) result
