(* This is the top-level driver for the proof assistant. *)

val load_file : [`Stdin | `File of string] -> (unit, unit) result
val do_repl : unit -> (unit, unit) result
