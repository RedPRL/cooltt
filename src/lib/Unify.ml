open CoolBasis

module D = Domain
module EM = ElabBasics

open Monad.Notation (EM)

let rec unify_tp : D.tp -> D.tp -> unit EM.m =
  fun tp0 tp1 ->
  match tp0, tp1 with
  | D.Pi (base0, fam0), D.Pi (base1, fam1) ->
    let* () = unify_tp base0 base1 in
    EM.abstract None base0 @@ fun x ->
    let* fib0 = EM.lift_cmp @@ Nbe.inst_tp_clo fam0 [x] in
    let* fib1 = EM.lift_cmp @@ Nbe.inst_tp_clo fam1 [x] in
    unify_tp fib0 fib1
  | _ ->
    failwith ""