module D = Domain
module S = Syntax
module CS = ConcreteSyntax
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module T = Tactic
module QQ = Quasiquote
module TB = TermBuilder

exception Todo

open CoolBasis
open Monads
open Monad.Notation (EM)
open Bwd

type ('a, 'b) quantifier = 'a -> CS.ident option * (T.var -> 'b) -> 'b

let rec int_to_term =
  function
  | 0 -> S.Zero
  | n -> S.Suc (int_to_term (n - 1))

module Hole =
struct
  let make_hole name flexity (tp, phi, clo) =
    let rec go_tp : Env.cell list -> S.tp m =
      function
      | [] ->
        EM.lift_qu @@ Nbe.quote_tp @@ D.GoalTp (name, D.Sub (tp, phi, clo))
      | cell :: cells ->
        let ctp, _ = Env.Cell.contents cell in
        let name = Env.Cell.name cell in
        let+ base = EM.lift_qu @@ Nbe.quote_tp ctp
        and+ fam = EM.push_var name ctp @@ go_tp cells in
        S.Pi (base, fam)
    in

    let rec go_tm cut : Env.cell bwd -> D.cut =
      function
      | Emp -> cut
      | Snoc (cells, cell) ->
        let tp, con = Env.Cell.contents cell in
        go_tm cut cells |> D.push @@ D.KAp (tp, con)
    in

    let* env = EM.read in
    let names = Pp.Env.names @@ Env.pp_env env in
    EM.globally @@
    let* sym =
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

    let cut = go_tm (D.Global sym, []) @@ Env.locals env in
    EM.ret (D.SubOut (D.push KGoalProj cut, phi, clo), [])

  let unleash_hole name flexity : T.bchk_tac =
    fun (tp, phi, clo) ->
    let* cut = make_hole name flexity (tp, phi, clo) in
    EM.lift_qu @@ Nbe.quote_cut cut

  let unleash_tp_hole name flexity : T.tp_tac =
    T.Tp.make @@
    let* cut = make_hole name flexity @@ (D.Univ, Cof.bot, D.const_tm_clo D.Abort) in
    EM.lift_qu @@ Nbe.quote_tp @@ D.El cut

  let unleash_syn_hole name flexity : T.syn_tac =
    let* tpcut = make_hole name `Flex @@ (D.Univ, Cof.bot, D.const_tm_clo D.Abort) in
    let+ tm = T.bchk_to_chk (unleash_hole name flexity) @@ D.El tpcut in
    tm, D.El tpcut
end


module Goal =
struct
  let formation lbl tac =
    T.Tp.make @@
    let+ tp = T.Tp.run tac in
    S.GoalTp (lbl, tp)
end


module Sub =
struct
  let formation (tac_base : T.tp_tac) (tac_phi : T.chk_tac) (tac_tm : T.chk_tac) : T.tp_tac =
    T.Tp.make @@
    let* base = T.Tp.run tac_base in
    let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
    let* phi = tac_phi D.TpCof in
    let+ tm =
      let* vphi = EM.lift_ev @@ Nbe.eval_cof phi in
      EM.push_var None (D.TpPrf vphi) @@ tac_tm vbase
    in
    S.Sub (base, phi, tm)

  let intro (tac : T.bchk_tac) : T.bchk_tac =
    function
    | D.Sub (tp_a, phi_a, clo_a), phi_sub, clo_sub ->
      let phi = Cof.join phi_a phi_sub in
      let* partial =
        EM.lift_cmp @@ Nbe.quasiquote_tm @@
        QQ.foreign_tp tp_a @@ fun tp_a ->
        QQ.foreign (D.cof_to_con phi_a) @@ fun phi_a ->
        QQ.foreign (D.cof_to_con phi_sub) @@ fun phi_sub ->
        QQ.foreign (D.Lam clo_a) @@ fun fn_a ->
        QQ.foreign (D.Lam clo_sub) @@ fun fn_sub ->
        QQ.term @@ TB.lam @@ fun prf ->
        TB.cof_split tp_a phi_a (fun prf -> TB.ap fn_a [prf]) phi_sub (fun prf -> TB.sub_out @@ TB.ap fn_sub [prf])
      in
      let+ tm = tac (tp_a, phi, D.un_lam partial) in
      S.SubIn tm
    | tp, _, _ ->
      EM.expected_connective `Sub tp

  let elim (tac : T.syn_tac) : T.syn_tac =
    let* tm, subtp = tac in
    match subtp with
    | D.Sub (tp, _, _) ->
      EM.ret (S.SubOut tm, tp)
    | tp ->
      EM.expected_connective `Sub tp
end

module Dim =
struct
  let formation : T.tp_tac =
    T.Tp.make_virtual @@
    EM.ret S.TpDim

  let dim0 : T.chk_tac =
    function
    | D.TpDim ->
      EM.ret S.Dim0
    | tp ->
      EM.expected_connective `Dim tp

  let dim1 : T.chk_tac =
    function
    | D.TpDim ->
      EM.ret S.Dim1
    | tp ->
      EM.expected_connective `Dim tp

  let literal : int -> T.chk_tac =
    function
    | 0 -> dim0
    | 1 -> dim1
    | n ->
      fun _ ->
        EM.elab_err @@ Err.ExpectedDimensionLiteral n
end

module Cof =
struct
  let formation : T.tp_tac =
    T.Tp.make_virtual @@
    EM.ret S.TpCof

  let expected_cof =
    EM.expected_connective `Cof

  let eq tac0 tac1 =
    function
    | D.TpCof ->
      let+ r0 = tac0 D.TpDim
      and+ r1 = tac1 D.TpDim in
      S.Cof (Cof.Eq (r0, r1))
    | tp ->
      expected_cof tp

  let join tac0 tac1 =
    function
    | D.TpCof ->
      let+ phi0 = tac0 D.TpCof
      and+ phi1 = tac1 D.TpCof in
      S.Cof (Cof.Join (phi0, phi1))
    | tp ->
      expected_cof tp

  let meet tac0 tac1 =
    function
    | D.TpCof ->
      let+ phi0 = tac0 D.TpCof
      and+ phi1 = tac1 D.TpCof in
      S.Cof (Cof.Meet (phi0, phi1))
    | tp ->
      expected_cof tp

  let assert_true vphi =
    EM.lift_cmp @@ CmpM.test_sequent [] vphi |>> function
    | true -> EM.ret ()
    | false ->
      EM.with_pp @@ fun ppenv ->
      let* tphi = EM.lift_qu @@ Nbe.quote_cof vphi in
      EM.elab_err @@ Err.ExpectedTrue (ppenv, tphi)


  type branch_tac = T.chk_tac * (T.var -> T.bchk_tac)

  let rec njoin : D.cof list -> D.cof =
     function
     | [] -> Cof.bot
     | phi :: phis -> Cof.join phi @@ njoin phis

  let rec gather_cofibrations (branches : branch_tac list) : (D.cof list * (T.var -> T.bchk_tac) list) m =
    match branches with
    | [] -> EM.ret ([], [])
    | (tac_phi, tac_tm) :: branches ->
      let* tphi = tac_phi D.TpCof in
      let* vphi = EM.lift_ev @@ Nbe.eval_cof tphi in
      let+ phis, tacs = gather_cofibrations branches in
      (vphi :: phis), tac_tm :: tacs

  let split0 : T.bchk_tac =
    fun _ ->
    let* _ = assert_true Cof.bot in
    EM.ret S.CofAbort

  let split1 (phi : D.cof) (tac : T.var -> T.bchk_tac) : T.bchk_tac =
    fun goal ->
    let* _ = assert_true phi in
    tac (T.Var.prf phi) goal

  let split2 (phi0 : D.cof) (tac0 : T.var -> T.bchk_tac) (phi1 : D.cof) (tac1 : T.var -> T.bchk_tac) : T.bchk_tac =
    fun (tp, psi, psi_clo) ->
    let* ttp = EM.lift_qu @@ Nbe.quote_tp tp in
    let* _ = assert_true @@ Cof.join phi0 phi1 in
    let* tm0 =
      T.abstract (D.TpPrf phi0) None @@ fun prf ->
      tac0 prf (tp, psi, psi_clo)
    in
    let* tm1 =
      T.abstract (D.TpPrf phi1) None @@ fun prf ->
      let psi' = Cof.join phi0 psi in
      let* phi0_fn = EM.lift_ev @@ Nbe.eval @@ S.Lam tm0 in
      let psi_fn = D.Lam psi_clo in
      let* psi'_fn =
        EM.lift_cmp @@ Nbe.quasiquote_tm @@
        QQ.foreign_tp tp @@ fun tp ->
        QQ.foreign (D.cof_to_con phi0) @@ fun phi0 ->
        QQ.foreign (D.cof_to_con psi) @@ fun psi ->
        QQ.foreign phi0_fn @@ fun phi0_fn ->
        QQ.foreign psi_fn @@ fun psi_fn ->
        QQ.term @@ TB.lam @@ fun prf ->
        TB.cof_split tp phi0 (fun prf -> TB.ap phi0_fn [prf]) psi (fun prf -> TB.ap psi_fn [prf])
      in
      tac1 prf (tp, psi', D.un_lam psi'_fn)
    in
    let* tphi0 = EM.lift_qu @@ Nbe.quote_cof phi0 in
    let* tphi1 = EM.lift_qu @@ Nbe.quote_cof phi1 in
    EM.ret @@ S.CofSplit (ttp, tphi0, tphi1, tm0, tm1)



  let rec gather_cofibrations (branches : branch_tac list) : (D.cof list * (T.var -> T.bchk_tac) list) m =
    match branches with
    | [] -> EM.ret ([], [])
    | (tac_phi, tac_tm) :: branches ->
      let* tphi = tac_phi D.TpCof in
      let* vphi = EM.lift_ev @@ Nbe.eval_cof tphi in
      let+ phis, tacs = gather_cofibrations branches in
      (vphi :: phis), tac_tm :: tacs

  let split (branches : branch_tac list) : T.bchk_tac =
    fun goal ->
    let* phis, tacs = gather_cofibrations branches in
    let disj_phi = njoin phis in
    let* _ = assert_true disj_phi in
    let rec go phis (tacs : (T.var -> T.bchk_tac) list) : T.bchk_tac =
      match phis, tacs with
      | [phi], [tac] ->
        split1 phi tac
      | phi :: phis, tac :: tacs ->
        split2 phi tac (njoin phis) (fun _ -> go phis tacs)
      | [], [] ->
        split0
      | _ -> failwith "internal error"
    in
    go phis tacs goal
end

module Prf =
struct
  let formation tac_phi =
    T.Tp.make_virtual @@
    let+ phi = tac_phi D.TpCof in
    S.TpPrf phi

  let intro =
    function
    | D.TpPrf phi, _, _ ->
      begin
        EM.lift_cmp @@ CmpM.test_sequent [] phi |>> function
        | true -> EM.ret S.Prf
        | false ->
          EM.with_pp @@ fun ppenv ->
          let* tphi = EM.lift_qu @@ Nbe.quote_cof phi in
          EM.elab_err @@ Err.ExpectedTrue (ppenv, tphi)
      end
    | tp, _, _ ->
      EM.expected_connective `Prf tp
end


module Id =
struct
  let formation (tac_tp : T.tp_tac) (tac0 : T.chk_tac) (tac1 : T.chk_tac) : T.tp_tac =
    T.Tp.make @@
    let* tp = T.Tp.run tac_tp in
    let* vtp = EM.lift_ev @@ Nbe.eval_tp tp in
    let+ tm0 = tac0 vtp
    and+ tm1 = tac1 vtp in
    S.Id (tp, tm0, tm1)

  let intro : T.chk_tac =
    function
    | D.Id (tp, l, r) ->
      let+ () = EM.equate tp l r
      and+ t = EM.lift_qu @@ Nbe.quote_con tp l in
      S.Refl t
    | tp ->
      EM.expected_connective `Id tp

  let elim (nm_x0, nm_x1, nm_p, tac_mot) (nm_x, tac_case_refl) tac_scrut : T.syn_tac =
    EM.push_problem "elim" @@
    let* tscrut, idtp = tac_scrut in
    let* tp, l, r = EM.dest_id idtp in
    let* tmot =
      EM.abstract nm_x0 tp @@ fun x0 ->
      EM.abstract nm_x1 tp @@ fun x1 ->
      EM.abstract nm_p (D.Id (tp, x0, x1)) @@ fun _ ->
      T.Tp.run tac_mot
    in
    let* t_refl_case =
      EM.abstract nm_x tp @@ fun x ->
      tac_case_refl @<<
      EM.lift_ev @@ EvM.append [x; D.Refl x] @@ Nbe.eval_tp tmot
    in
    let+ fib =
      let* vscrut = EM.lift_ev @@ Nbe.eval tscrut in
      EM.lift_ev @@ EvM.append [l; r; vscrut] @@ Nbe.eval_tp tmot
    in
    S.IdElim (tmot, t_refl_case, tscrut), fib
end

module Pi =
struct
  let formation : (T.tp_tac, T.tp_tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.make @@
      let* base = T.Tp.run_virtual tac_base in
      let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
      let+ fam = T.abstract vbase nm @@ fun var -> T.Tp.run @@ tac_fam var in
      S.Pi (base, fam)

  let intro name (tac_body : T.var -> T.bchk_tac) : T.bchk_tac =
    function
    | D.Pi (base, fam), phi, phi_clo ->
      T.abstract base name @@ fun var ->
      let* fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [T.Var.con var] in
      let+ tm = tac_body var (fib, phi, D.un_lam @@ D.compose (D.Lam (D.apply_to (T.Var.con var))) @@ D.Lam phi_clo) in
      S.Lam tm
    | tp, _, _ ->
      EM.expected_connective `Pi tp

  let apply tac_fun tac_arg : T.syn_tac =
    let* tfun, tp = tac_fun in
    let* base, fam = EM.dest_pi tp in
    let* targ = tac_arg base in
    let+ fib =
      let* varg = EM.lift_ev @@ Nbe.eval targ in
      EM.lift_cmp @@ Nbe.inst_tp_clo fam [varg]
    in
    S.Ap (tfun, targ), fib
end

module Sg =
struct
  let formation : (T.tp_tac, T.tp_tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.make @@
      let* base = T.Tp.run tac_base in
      let* vbase = EM.lift_ev @@ Nbe.eval_tp base in
      let+ fam = T.abstract vbase nm @@ fun var -> T.Tp.run @@ tac_fam var in
      S.Sg (base, fam)

  let intro (tac_fst : T.bchk_tac) (tac_snd : T.bchk_tac) : T.bchk_tac =
    function
    | D.Sg (base, fam), phi, phi_clo ->
      let* tfst = tac_fst (base, phi, D.un_lam @@ D.compose D.fst @@ D.Lam phi_clo) in
      let+ tsnd =
        let* vfst = EM.lift_ev @@ Nbe.eval tfst in
        let* fib = EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst] in
        tac_snd (fib, phi, D.un_lam @@ D.compose D.snd @@ D.Lam phi_clo)
      in
      S.Pair (tfst, tsnd)
    | tp , _, _ ->
      EM.expected_connective `Sg tp

  let pi1 tac : T.syn_tac =
    let* tpair, tp = tac in
    let+ base, _ = EM.dest_sg tp in
    S.Fst tpair, base

  let pi2 tac : T.syn_tac =
    let* tpair, tp = tac in
    let+ fib =
      let* vfst = EM.lift_ev @@ Nbe.eval @@ S.Fst tpair in
      let* _, fam = EM.dest_sg tp in
      EM.lift_cmp @@ Nbe.inst_tp_clo fam [vfst]
    in
    S.Snd tpair, fib
end



module Univ =
struct
  let formation : T.tp_tac =
    T.Tp.make @@
    EM.ret S.Univ

  let el_formation tac =
    T.Tp.make @@
    let+ tm = tac D.Univ in
    S.El tm

  let univ_tac : T.chk_tac -> T.chk_tac =
    fun m ->
    function
    | D.Univ -> m D.Univ
    | tp ->
      EM.expected_connective `Univ tp

  let nat : T.chk_tac =
    univ_tac @@ fun _ -> EM.ret S.CodeNat

  let quantifier tac_base tac_fam =
    fun univ ->
    let* base = tac_base univ in
    let* vbase = EM.lift_ev @@ Nbe.eval base in
    let* famtp =
      EM.lift_cmp @@
      Nbe.quasiquote_tp @@
      QQ.foreign vbase @@ fun base ->
      QQ.foreign_tp univ @@ fun univ ->
      QQ.term @@ TB.pi (TB.el base) @@ fun _ -> univ
    in
    let+ fam = tac_fam famtp in
    base, fam

  let pi tac_base tac_fam : T.chk_tac =
    univ_tac @@ fun univ ->
    let+ tp, fam = quantifier tac_base tac_fam univ in
    S.CodePi (tp, fam)

  let sg tac_base tac_fam : T.chk_tac =
    univ_tac @@ fun univ ->
    let+ tp, fam = quantifier tac_base tac_fam univ in
    S.CodeSg (tp, fam)

  let path (tac_fam : T.chk_tac) (tac_bdry : T.chk_tac) : T.chk_tac =
    univ_tac @@ fun univ ->
    let* piuniv =
        EM.lift_cmp @@
        Nbe.quasiquote_tp @@
        QQ.foreign_tp univ @@ fun univ ->
        QQ.term @@
        TB.pi TB.tp_dim @@ fun i ->
        univ
    in
    let* fam = tac_fam piuniv in (* build a term at the type and call the tactic on that type *)
    let* vfam = EM.lift_ev (Nbe.eval fam) in 
    let* bdry_tp =
        EM.lift_cmp @@
        Nbe.quasiquote_tp @@
        QQ.foreign_tp univ @@ fun univ ->
        QQ.foreign vfam @@ fun fam ->
        QQ.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.pi (TB.tp_prf (TB.boundary i)) @@ fun prf ->
        TB.el @@ TB.ap fam [i] in
    let* bdry = tac_bdry bdry_tp in
    EM.ret @@ S.CodePath(fam, bdry)

  (* TODO: the derived rule *)
  let path_with_endpoints (tac_fam : T.chk_tac) (tac_a : T.bchk_tac) (tac_b : T.bchk_tac) : T.chk_tac =
    path tac_fam @@ 
    T.bchk_to_chk @@ 
    Pi.intro None @@ fun i ->
    Pi.intro None @@ fun pf ->
    Cof.split [(Cof.eq (T.syn_to_chk (T.Var.syn i)) Dim.dim0, fun _ -> tac_a);
               (Cof.eq (T.syn_to_chk (T.Var.syn i)) Dim.dim1, fun _ -> tac_b)]
end



module Structural =
struct
  let lookup_var id : T.syn_tac =
    let* res = EM.resolve id in
    match res with
    | `Local ix ->
      let+ tp = EM.get_local_tp ix in
      S.Var ix, tp
    | `Global sym ->
      let+ tp, _ = EM.get_global sym in
      S.Global sym, tp
    | `Unbound ->
      EM.elab_err @@ Err.UnboundVariable id

  let index ix =
    let+ tp = EM.get_local_tp ix in
    S.Var ix, tp

  let level lvl =
    let* env = EM.read in
    let ix = ElabEnv.size env - lvl - 1 in
    index ix

  let let_ tac_def (nm_x, (tac_bdy : T.var -> T.bchk_tac)) : T.bchk_tac =
    fun tp ->
    let* tdef, tp_def = tac_def in
    let* vdef = EM.lift_ev @@ Nbe.eval tdef in
    T.let_ tp_def vdef nm_x @@ fun x ->
    let+ tbdy = tac_bdy x tp in
    S.Let (tdef, tbdy)
end


module Nat =
struct
  let formation =
    T.Tp.make @@
    EM.ret S.Nat

  let assert_nat =
    function
    | D.Nat -> EM.ret ()
    | tp -> EM.expected_connective `Nat tp

  let literal n : T.chk_tac =
    fun tp ->
    let+ () = assert_nat tp in
    int_to_term n

  let suc tac : T.chk_tac =
    fun tp ->
    let* () = assert_nat tp in
    let+ t = tac tp in
    S.Suc t

  let elim (nm_mot, tac_mot) tac_case_zero (nm_x, nm_ih, tac_case_suc) tac_scrut : T.syn_tac =
    EM.push_problem "elim" @@
    let* tscrut, nattp = tac_scrut in
    let* () = assert_nat nattp in

    let* tmot =
      EM.abstract nm_mot nattp @@ fun _ ->
      T.Tp.run tac_mot
    in

    let* tcase_zero =
      tac_case_zero @<<
      EM.lift_ev @@ EvM.append [D.Zero] @@ Nbe.eval_tp tmot
    in

    let* tcase_suc =
      EM.abstract nm_x nattp @@ fun x ->
      let* fib_x = EM.lift_ev @@ EvM.append [x] @@ Nbe.eval_tp tmot in
      let* fib_suc_x = EM.lift_ev @@ EvM.append [D.Suc x] @@ Nbe.eval_tp tmot in
      EM.abstract nm_ih fib_x @@ fun _ ->
      tac_case_suc fib_suc_x
    in

    let+ fib_scrut =
      let* vscrut = EM.lift_ev @@ Nbe.eval tscrut in
      EM.lift_ev @@ EvM.append [vscrut] @@ Nbe.eval_tp tmot
    in
    S.NatElim (tmot, tcase_zero, tcase_suc, tscrut), fib_scrut
end



module Tactic =
struct
  let match_goal tac =
    fun goal ->
      let* tac = tac goal in
      tac goal

  let bmatch_goal = match_goal

  let rec tac_lam name tac_body : T.bchk_tac =
    match_goal @@ function
    | D.Pi _, _, _ ->
      EM.ret @@ Pi.intro name tac_body
    | D.Sub _, _, _ ->
      EM.ret @@ Sub.intro @@ tac_lam name tac_body
    | _ ->
      EM.throw @@ Invalid_argument "tac_lam cannot be called on this goal"

  let rec tac_multi_lam names tac_body =
    match names with
    | [] -> tac_body
    | name :: names ->
      tac_lam (Some name) @@ fun _ ->
      tac_multi_lam names tac_body

  let rec tac_multi_apply tac_fun =
    function
    | [] -> tac_fun
    | tac :: tacs ->
      tac_multi_apply (Pi.apply tac_fun tac) tacs

  let rec tac_nary_quantifier (quant : ('a, 'b) quantifier) cells body =
    match cells with
    | [] -> body
    | (nm, tac) :: cells ->
      quant tac (nm, fun _ -> tac_nary_quantifier quant cells body)

  module Elim =
  struct
    type case_tac = CS.pat * T.chk_tac

    let rec find_case (lbl : CS.ident) (cases : case_tac list) : (CS.pat_arg list * T.chk_tac) option =
      match cases with
      | (CS.Pat pat, tac) :: _ when pat.lbl = lbl ->
        Some (pat.args, tac)
      | _ :: cases ->
        find_case lbl cases
      | [] ->
        None

    let elim (mot : CS.ident option list * T.tp_tac) (cases : case_tac list) (scrut : T.syn_tac) : T.syn_tac =
      let* tscrut, ind_tp = scrut in
      let scrut = EM.ret (tscrut, ind_tp) in
      match ind_tp, mot with
      | D.Id (_, _, _), ([nm_u; nm_v; nm_p], mot) ->
        let* tac_refl =
          match find_case "refl" cases with
          | Some ([`Simple nm_w], tac) -> EM.ret (nm_w, tac)
          | Some ([], tac) -> EM.ret (None, tac)
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret (None, T.bchk_to_chk @@ Hole.unleash_hole (Some "refl") `Rigid)
        in
        Id.elim (nm_u, nm_v, nm_p, mot) tac_refl scrut
      | D.Nat, ([nm_x], mot) ->
        let* tac_zero =
          match find_case "zero" cases with
          | Some ([], tac) -> EM.ret tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ T.bchk_to_chk @@ Hole.unleash_hole (Some "zero") `Rigid
        in
        let* tac_suc =
          match find_case "suc" cases with
          | Some ([`Simple nm_z], tac) -> EM.ret (nm_z, None, tac)
          | Some ([`Inductive (nm_z, nm_ih)], tac) -> EM.ret (nm_z, nm_ih, tac)
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ (None, None, T.bchk_to_chk @@ Hole.unleash_hole (Some "suc") `Rigid)
        in
        Nat.elim (nm_x, mot) tac_zero tac_suc scrut
      | _ ->
        EM.with_pp @@ fun ppenv ->
        let* tp = EM.lift_qu @@ Nbe.quote_tp ind_tp in
        EM.elab_err @@ Err.CannotEliminate (ppenv, tp)

    let assert_simple_inductive =
      function
      | D.Nat ->
        EM.ret ()
      | tp ->
        EM.with_pp @@ fun ppenv ->
        let* tp = EM.lift_qu @@ Nbe.quote_tp tp in
        EM.elab_err @@ Err.ExpectedSimpleInductive (ppenv, tp)

    let lam_elim cases : T.bchk_tac =
      match_goal @@ fun (tp, _, _) ->
      let* base, fam = EM.dest_pi tp in
      let+ () = assert_simple_inductive base in
      let mot_tac : T.tp_tac =
        T.Tp.make @@
        let x = S.Var 0 in
        let* vx = EM.lift_ev @@ Nbe.eval x in
        let* vmot = EM.lift_cmp @@ Nbe.inst_tp_clo fam [vx] in
        EM.lift_qu @@ Nbe.quote_tp vmot
      in
      Pi.intro None @@ fun x ->
      T.chk_to_bchk @@
      T.syn_to_chk @@
      elim ([None], mot_tac) cases @@
      T.Var.syn x
  end
end
