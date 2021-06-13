open Basis
open Bwd
open Z3Monad
open Monad.Notation (Z3Monad)
module MU = Monad.Util (Z3Monad)

type t = Assertion.t bwd

exception Z3Failure

let empty = Emp

let assume thy cof = Snoc (thy, Assertion.of_cof cof)

let assert_ thy : unit m =
  add_assertions (Bwd.to_list thy)

let test_sequent thy goal =
  run_exn @@
  let* () = assert_ thy in
  let negated_goal = Assertion.of_negated_cof goal in
  check [negated_goal] |>> function
  | UNSATISFIABLE -> ret true
  | SATISFIABLE -> ret false
  | _ -> throw Z3Failure

let consistency thy =
  run_exn @@
  let* () = assert_ thy in
  check [] |>> function
  | UNSATISFIABLE -> ret `Consistent
  | SATISFIABLE -> ret `Inconsistent
  | _ -> throw Z3Failure

let assume_vars thy vars =
  List.fold_left (fun thy v -> Snoc (thy, Assertion.of_cof (Var v))) thy vars
