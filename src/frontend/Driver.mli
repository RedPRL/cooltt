(* This is the top-level driver for the proof assistant. *)

val load_file : as_file:string option -> [`Stdin | `File of string] -> (unit, unit) result
val do_repl : as_file:string option -> (unit, unit) result
