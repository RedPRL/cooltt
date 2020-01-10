module D = Domain
module S = Syntax
module CS = ConcreteSyntax
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics

open CoolBasis
open Monads
open Monad.Notation (EM)
open Bwd

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m
type quantifier_tac = tp_tac -> CS.ident option * tp_tac -> tp_tac

let rec int_to_term =
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module Hole =
struct
  let make_hole name flexity tp = 
    let rec go_tp : Env.cell list -> S.tp m =
      function
      | [] ->
        EM.lift_qu @@ Nbe.quote_tp @@ D.GoalTp (name, tp)
      | (D.Nf cell, name) :: cells ->
        let+ base = EM.lift_qu @@ Nbe.quote_tp cell.tp
        and+ fam = EM.push_var name cell.tp @@ go_tp cells in
        S.Pi (base, fam)
    in

    let rec go_tm cut : Env.cell bwd -> D.cut =
      function
      | Emp -> cut
      | Snoc (cells, (D.Nf nf, _)) ->
        go_tm cut cells |> D.push @@ D.KAp (nf.tp, nf.con)
    in

    let* env = EM.read in
    let names = Pp.Env.names @@ Env.pp_env env in
    EM.globally @@
    let+ sym =
      let* tp = go_tp @@ Bwd.to_list @@ Env.locals env in
      let* () =
        () |> EM.emit @@ fun fmt () ->
        Format.fprintf fmt "Emitted hole:@,  @[<v>%a@]@." (S.pp_sequent ~names) tp
      in
      let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
      match flexity with
      | `Flex -> EM.add_flex_global vtp
      | `Rigid -> EM.add_global name vtp None
    in

    D.push D.KGoalProj @@ go_tm (D.Global sym, []) @@ Env.locals env 

  let unleash_hole name flexity : chk_tac =
    fun tp ->
    let* cut = make_hole name flexity tp in 
    EM.lift_qu @@ Nbe.quote_cut cut

  let unleash_tp_hole name flexity : tp_tac =
    let* cut = make_hole name flexity D.Univ in 
    EM.lift_qu @@ Nbe.quote_tp (D.El cut)

  let unleash_syn_hole name flexity : syn_tac =
    let* tpcut = make_hole name `Flex D.Univ in 
    let+ tm = unleash_hole name flexity @@ D.El tpcut in
    tm, D.El tpcut
end


module Goal = 
struct
  let formation lbl tac =
    let+ tp = tac in
    S.GoalTp (lbl, tp)
end


module Univ = 
struct
  let formation : tp_tac = 
    EM.ret S.Univ

  let dest_univ =
    function
    | D.Univ -> EM.ret ()
    | tp -> EM.elab_err @@ Err.ExpectedConnective (`Univ, tp)

  let nat : chk_tac =
    fun tp ->
    let* () = dest_univ tp in
    EM.ret S.CodeNat

end

module Id = 
struct
  let formation tac_tp tac_l tac_r =
    let* tp = tac_tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
    let+ l = tac_l vtp
    and+ r = tac_r vtp in
    S.Id (tp, l, r)

  let intro : chk_tac =
    function
    | D.Id (tp, l, r) ->
      let+ () = EM.equate tp l r
      and+ t = EM.lift_qu @@ Nbe.quote_con tp l in
      S.Refl t
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`Id, tp)

  let elim (nm_x0, nm_x1, nm_p, tac_mot) (nm_x, tac_case_refl) tac_scrut : syn_tac =
    let* tscrut, idtp = tac_scrut in
    let* vscrut = EM.lift_ev @@ Nbe.eval tscrut in
    let* tp, l, r = EM.dest_id idtp in
    let* tmot =
      EM.abstract nm_x0 tp @@ fun x0 ->
      EM.abstract nm_x1 tp @@ fun x1 ->
      EM.abstract nm_p (Id (tp, x0, x1)) @@ fun _ ->
      tac_mot
    in
    let* t_refl_case =
      EM.abstract nm_x tp @@ fun x ->
      let* fib_refl_x = EM.lift_ev @@ EvM.append [x; D.Refl x] @@ Nbe.eval_tp tmot in
      tac_case_refl fib_refl_x
    in
    let+ fib = EM.lift_ev @@ EvM.append [l; r; vscrut] @@ Nbe.eval_tp tmot in
    S.IdElim (tmot, t_refl_case, tscrut), fib
end


module Pi =
struct 
  let formation tac_base (nm, tac_fam) =
    let* base = tac_base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var nm vbase tac_fam in
    S.Pi (base, fam)

  let intro name tac_body : chk_tac =
    function
    | D.Pi (base, fam) ->
      EM.abstract name base @@ fun var ->
      let* fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [var] in
      let+ t = tac_body fib in
      S.Lam t
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`Pi, tp)

  let apply tac_fun tac_arg : syn_tac =
    let* tfun, tp = tac_fun in
    let* base, fam = EM.dest_pi tp in
    let* targ = tac_arg base in
    let* varg = EM.lift_ev @@ Nbe.eval targ in
    let+ fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [varg] in
    S.Ap (tfun, targ), fib
end

module Sg = 
struct
  let formation tac_base (nm, tac_fam) =
    let* base = tac_base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let+ fam = EM.push_var nm vbase tac_fam in
    S.Sg (base, fam)

  let intro tac_fst tac_snd : chk_tac =
    function
    | D.Sg (base, fam) ->
      let* tfst = tac_fst base in
      let* vfst = EM.lift_ev @@ Nbe.eval tfst in
      let* fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst] in
      let+ tsnd = tac_snd fib in
      S.Pair (tfst, tsnd)
    | tp ->
      EM.elab_err @@ Err.ExpectedConnective (`Sg, tp)

  let pi1 tac : syn_tac =
    let* tpair, tp = tac in
    let+ base, _ = EM.dest_sg tp in
    S.Fst tpair, base

  let pi2 tac : syn_tac =
    let* tpair, tp = tac in
    let* vfst = EM.lift_ev @@ Nbe.eval @@ S.Fst tpair in
    let* _, fam = EM.dest_sg tp in
    let+ fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst] in
    S.Snd tpair, fib
end


module Nat = 
struct
  let formation = 
    EM.ret S.Nat

  let assert_nat =
    function
    | D.Nat -> EM.ret ()
    | tp -> EM.elab_err @@ Err.ExpectedConnective (`Nat, tp)

  let literal n : chk_tac =
    fun tp ->
    let* () = assert_nat tp in
    EM.ret @@ int_to_term n

  let suc tac : chk_tac =
    fun tp ->
    let* () = assert_nat tp in
    let+ t = tac tp in
    S.Suc t

  let elim (nm_mot, tac_mot) tac_case_zero (nm_x, nm_ih, tac_case_suc) tac_scrut : syn_tac =
    let* tscrut, nattp = tac_scrut in
    let* () = assert_nat nattp in
    let* vscrut = EM.lift_ev @@ Nbe.eval tscrut in

    let* tmot =
      EM.abstract nm_mot nattp @@ fun _ ->
      tac_mot
    in

    let* tcase_zero =
      let* fib_zero = EM.lift_ev @@ EvM.append [D.Zero] @@ Nbe.eval_tp tmot in
      tac_case_zero fib_zero
    in

    let* tcase_suc =
      EM.abstract nm_x nattp @@ fun x ->
      let* fib_x = EM.lift_ev @@ EvM.append [x] @@ Nbe.eval_tp tmot in
      let* fib_suc_x = EM.lift_ev @@ EvM.append [D.Suc x] @@ Nbe.eval_tp tmot in
      EM.abstract nm_ih fib_x @@ fun _ ->
      tac_case_suc fib_suc_x
    in

    let+ fib_scrut = EM.lift_ev @@ EvM.append [vscrut] @@ Nbe.eval_tp tmot in
    S.NatElim (tmot, tcase_zero, tcase_suc, tscrut), fib_scrut
end

module El =
struct
  let formation tac = 
    let+ tm = tac D.Univ in 
    S.El tm
end

module Structural = 
struct
  let syn_to_chk (tac : syn_tac) : chk_tac =
    fun tp ->
      let* tm, tp' = tac in
      let+ () = Unify.unify_tp tp tp' in
      tm

  let chk_to_syn (tac_tm : chk_tac) (tac_tp : tp_tac) : syn_tac =
    let* tp = tac_tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
    let+ tm = tac_tm vtp in
    tm, vtp

  let lookup_var id : syn_tac =
    let* res = EM.resolve id in
    match res with
    | `Local ix ->
      let+ tp = EM.get_local_tp ix in
      S.Var ix, tp
    | `Global sym ->
      let+ D.Nf {tp; _} = EM.get_global sym in
      S.Global sym, tp
    | `Unbound ->
      EM.elab_err @@ Err.UnboundVariable id



  let let_ tac_def (nm_x, tac_bdy) : chk_tac =
    fun tp ->
    let* tdef, tp_def = tac_def in
    let* vdef = EM.lift_ev @@ Nbe.eval tdef in
    EM.define nm_x tp_def vdef @@ fun _ ->
    let+ tbdy = tac_bdy tp in
    S.Let (tdef, tbdy)
end

module Tactic =
struct
  let rec tac_multi_lam names tac_body =
    match names with
    | [] -> tac_body
    | name :: names ->
      Pi.intro (Some name) @@
      tac_multi_lam names tac_body

  let rec tac_multi_apply tac_fun =
    function
    | [] -> tac_fun
    | tac :: tacs ->
      tac_multi_apply (Pi.apply tac_fun tac) tacs

  let rec tac_nary_quantifier (quant : quantifier_tac) cells body = 
    match cells with
    | [] -> body
    | (nm, tac) :: cells -> 
      quant tac (nm, tac_nary_quantifier quant cells body)
end