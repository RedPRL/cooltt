open CoolBasis

module D = Domain
module EM = ElabBasics
module St = ElabState

open Monad.Notation (EM)

exception UnificationError

let eta_contract : D.con -> int EM.m =
  function
  | D.Cut {cut = (D.Var lvl, []), _; _} ->
    EM.ret lvl
  | _ -> 
    EM.throw UnificationError

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
  | D.GoalTp (lbl0, tp0), D.GoalTp (lbl1, tp1) when lbl0 = lbl1 ->
    unify_tp tp0 tp1
  | D.El (D.Global sym0, spine0), _ ->
    unify_tp_cut_with_tp (sym0, spine0) tp1
  | _, D.El (D.Global sym1, spine1) ->
    unify_tp_cut_with_tp (sym1, spine1) tp0
  | _ ->
    EM.throw UnificationError


and unify_tp_cut_with_tp (sym0, spine0) tp1 = 
  let* st = EM.get in
  match St.get_flexity sym0 st with
  | `Flex ->
    begin
      match tp1 with 
      | D.El (D.Global sym1, spine1) when St.get_flexity sym1 st = `Flex -> 
        unify_tp_flex_flex (sym0, spine0) (sym1, spine1)
      | _ -> 
        unify_tp_flex_rigid (sym0, spine0) tp1
    end
  | `Rigid ->
    begin
      match tp1 with
      | D.El (D.Global sym1, spine1) when St.get_flexity sym1 st = `Flex -> 
        unify_tp_flex_rigid (sym1, spine1) tp1
      | D.El (D.Global sym1, spine1) when St.get_flexity sym1 st = `Rigid ->
        unify_tp_rigid_rigid (sym0, spine0) (sym1, spine1)
      | _ -> 
        EM.throw UnificationError
    end

and unify_tp_flex_rigid (sym0, spine0) tp1 =
  (* TODO *)
  EM.lift_qu @@ 
  Nbe.equate_tp
    (D.El (D.Global sym0, spine0) )
    tp1


and unify_tp_flex_flex (sym0, spine0) (sym1, spine1) =
  (* TODO *)
  EM.lift_qu @@ 
  Nbe.equate_cut 
    (D.Global sym0, spine0) 
    (D.Global sym1, spine1)

and unify_tp_rigid_rigid (sym0, spine0) (sym1, spine1) =
  (* TODO *)
  EM.lift_qu @@ 
  Nbe.equate_cut 
    (D.Global sym0, spine0) 
    (D.Global sym1, spine1)