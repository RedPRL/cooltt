open CoolBasis

module D = Domain
module EM = ElabBasics

open Monad.Notation (EM)

exception UnificationError

let rec unify_tp : D.tp -> D.tp -> unit EM.m =
  fun tp0 tp1 ->
  match tp0, tp1 with
  | D.Pi (base0, fam0), D.Pi (base1, fam1) ->
    let* () = unify_tp base0 base1 in
    EM.abstract None base0 @@ fun x ->
    let* fib0 = EM.lift_cmp @@ Nbe.inst_tp_clo fam0 [x] in
    let* fib1 = EM.lift_cmp @@ Nbe.inst_tp_clo fam1 [x] in
    unify_tp fib0 fib1
  | D.Sg (base0, fam0), D.Sg (base1, fam1) ->
    let* () = unify_tp base0 base1 in
    EM.abstract None base0 @@ fun x ->
    let* fib0 = EM.lift_cmp @@ Nbe.inst_tp_clo fam0 [x] in
    let* fib1 = EM.lift_cmp @@ Nbe.inst_tp_clo fam1 [x] in
    unify_tp fib0 fib1
  | D.Id (tp0, l0, r0), D.Id (tp1, l1, r1) ->
    let* () = unify_tp tp0 tp1 in
    let* () = EM.lift_qu @@ Nbe.equate_con tp0 l0 l1 in (* TODO, unify *)
    EM.lift_qu @@ Nbe.equate_con tp0 r0 r1 (* TODO, unify *)
  | D.Nat, D.Nat -> 
    EM.ret ()
  | D.Univ, D.Univ -> 
    EM.ret ()
  | D.El cut0, D.El cut1 ->
    EM.lift_qu @@ Nbe.equate_cut cut0 cut1 (* TODO: check for flex *)
  | _ ->
    EM.throw UnificationError