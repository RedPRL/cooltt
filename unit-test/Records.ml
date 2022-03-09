open Basis
open Core
open Frontend

open Framework

open Monad.Notation (RM)

let () =
  let open Alcotest in
  Debug.debug_mode true;
  run "Records" [
    "Telescope Elimination", []
  ]
