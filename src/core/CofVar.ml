open Basis

module Make (Symbol : Symbol.S) =
struct

  type t =
    | Local of int
    | Axiom of Symbol.t

  let compare v0 v1 =
    match v0, v1 with
    | Local lvl0, Local lvl1 -> Int.compare lvl0 lvl1
    | Axiom sym0, Axiom sym1 -> Symbol.compare sym0 sym1
    | Local _, Axiom _ -> -1
    | Axiom _, Local _ -> 1

  let dump fmt =
    function
    | Local lvl -> Format.pp_print_int fmt lvl
    | Axiom sym -> Symbol.pp fmt sym
end
