(* This is the top-level driver for the proof assistant. *)
val process_file : input:string option -> (unit, unit) result
val do_repl : input:string option -> (unit, unit) result
