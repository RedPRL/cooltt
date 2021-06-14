include Basis.Monad.S
val throw : exn -> 'a m
val run : 'a m -> ('a, exn) result
val run_exn : 'a m -> 'a

type check_result = Z3.Solver.status =
    UNSATISFIABLE | UNKNOWN | SATISFIABLE

val add_cofs : CofThyData.cof list -> unit m
val add_negated_cof : CofThyData.cof -> unit m
val check : unit -> check_result m

val dump_solver : unit -> unit m
val get_reason_unknown : unit -> string m
