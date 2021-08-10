(* This is the top-level driver for the proof assistant. *)

type options =
  { as_file : string option;
    debug_mode : bool;
    server_port : int option }

val load_file : options -> [`Stdin | `File of string] -> (unit, unit) result
val do_repl : options -> (unit, unit) result
