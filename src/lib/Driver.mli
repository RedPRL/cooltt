(* This is the top-level driver for the proof assistant. Given
 * a signature (a list of commands/declarations) process each
 * command in sequence *)
val process_sign : ConcreteSyntax.signature -> (unit, unit) result
