module Assertion :
sig
  type t = Z3.Expr.expr
  val of_cof : CofThyData.cof -> t
  val of_negated_cof : CofThyData.cof -> t
end

include Basis.Monad.S
val throw : exn -> 'a m
val run : 'a m -> ('a, exn) result
val run_exn : 'a m -> 'a

type check_result = Z3.Solver.status =
    UNSATISFIABLE | UNKNOWN | SATISFIABLE

val add_assertions : Assertion.t list -> unit m
val check : Assertion.t list -> check_result m
