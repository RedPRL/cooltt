(* This is the top-level driver for the proof assistant. *)
open Basis
open Core

type options =
  { as_file : string option;
    debug_mode : bool;
  }

val load_file : options -> [`Stdin | `File of string] -> (unit, unit) result
val do_repl : options -> (unit, unit) result
