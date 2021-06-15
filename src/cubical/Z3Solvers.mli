module type S =
sig
  type check_result = Z3.Solver.status =
      UNSATISFIABLE | UNKNOWN | SATISFIABLE
  val test_sequent : ?rhs:CofThyData.cof -> lhs:CofThyData.cof list -> check_result
  val get_reason_unknown : unit -> string
end

module BoolSolver : S
module RealSolver : S
