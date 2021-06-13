module Assertion :
sig
  type t
  val of_cof : CofThyData.cof -> t
  val of_negated_cof : CofThyData.cof -> t
  val complexity : t -> int
  val dump : t Basis.Pp.printer
end

include Basis.Monad.S
val throw : exn -> 'a m
val run : 'a m -> ('a, exn) result
val run_exn : 'a m -> 'a

type check_result = Z3.Solver.status =
    UNSATISFIABLE | UNKNOWN | SATISFIABLE

val reset : unit -> unit m
val add_assertions : Assertion.t list -> unit m
val check : unit -> check_result m

val dump_solver : unit -> unit m
val get_reason_unknown : unit -> string m
