module D = Domain
module S = Syntax
module CS = ConcreteSyntax
module Env = ElabEnv
module Err = ElabError
module EM = ElabBasics
module T = Tactic
module Splice = Splice
module TB = TermBuilder
module Sem = Semantics
module Qu = Quote
module Cofibration = Cof (* this lets us access Cof after it gets shadowed below *)

exception Todo

open CoolBasis
open Monads
open Monad.Notation (EM)
module MU = Monad.Util (EM)
open Bwd

type ('a, 'b) quantifier = 'a -> CS.ident option * (T.var -> 'b) -> 'b

module Hole : sig
  val unleash_hole : CS.ident option -> [`Flex | `Rigid] -> T.bchk_tac
  val unleash_tp_hole : CS.ident option -> [`Flex | `Rigid] -> T.tp_tac
  val unleash_syn_hole : CS.ident option -> [`Flex | `Rigid] -> T.syn_tac
end =
struct
  let make_hole name flexity (tp, phi, clo) : D.cut m =
    let rec go_tp : Env.cell list -> S.tp m =
      function
      | [] ->
        EM.lift_qu @@ Qu.quote_tp @@ D.GoalTp (name, D.Sub (tp, phi, clo))
      | cell :: cells ->
        let ctp, _ = Env.Cell.contents cell in
        let name = Env.Cell.name cell in
        let+ base = EM.lift_qu @@ Qu.quote_tp ctp
        and+ fam = EM.abstract name ctp @@ fun _ -> go_tp cells in
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
        () |> EM.emit (ElabEnv.location env) @@ fun fmt () ->
        Format.fprintf fmt "Emitted hole:@,  @[<v>%a@]@." (S.pp_sequent ~names) tp
      in
      let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
      match flexity with
      | `Flex -> EM.add_flex_global vtp
      | `Rigid -> EM.add_global name vtp None
    in

    let cut = go_tm (D.Global sym, []) @@ Env.locals env in
    EM.ret (D.SubOut (D.push KGoalProj cut, phi, clo), [])

  let unleash_hole name flexity : T.bchk_tac =
    fun (tp, phi, clo) ->
    let* cut = make_hole name flexity (tp, phi, clo) in
    EM.lift_qu @@ Qu.quote_cut cut

  let unleash_tp_hole name flexity : T.tp_tac =
    T.Tp.make @@
    let* cut = make_hole name flexity @@ (D.Univ, Cof.bot, D.Clo (S.CofAbort, {tpenv = Emp; conenv = Emp})) in
    EM.lift_qu @@ Qu.quote_tp @@ D.El (D.Cut {tp = D.Univ; cut})

  let unleash_syn_hole name flexity : T.syn_tac =
    let* cut = make_hole name `Flex @@ (D.Univ, Cof.bot, D.Clo (S.CofAbort, {tpenv = Emp; conenv = Emp})) in
    let tp = D.El (D.Cut {tp = D.Univ; cut}) in
    let+ tm = T.Chk.bchk (unleash_hole name flexity) tp in
    tm, tp
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
  let formation (tac_base : T.tp_tac) (tac_phi : T.chk_tac) (tac_tm : T.var -> T.chk_tac) : T.tp_tac =
    T.Tp.make @@
    let* base = T.Tp.run tac_base in
    let* vbase = EM.lift_ev @@ Sem.eval_tp base in
    let* phi = tac_phi D.TpCof in
    let+ tm =
      let* vphi = EM.lift_ev @@ Sem.eval_cof phi in
      T.abstract (D.TpPrf vphi) None @@ fun prf ->
      tac_tm prf vbase
    in
    S.Sub (base, phi, tm)

  let intro (tac : T.bchk_tac) : T.bchk_tac =
    function
    | D.Sub (tp_a, phi_a, clo_a), phi_sub, clo_sub ->
      let phi = Cof.join [phi_a; phi_sub] in
      let* partial =
        EM.lift_cmp @@ Sem.splice_tm @@
        Splice.foreign_tp tp_a @@ fun tp_a ->
        Splice.foreign_cof phi_a @@ fun phi_a ->
        Splice.foreign_cof phi_sub @@ fun phi_sub ->
        Splice.foreign_clo clo_a @@ fun fn_a ->
        Splice.foreign_clo clo_sub @@ fun fn_sub ->
        Splice.term @@ TB.lam @@ fun prf ->
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

  let join tacs =
    function
    | D.TpCof ->
      let+ phis = MU.map (fun t -> t D.TpCof) tacs in
      S.Cof (Cof.Join phis)
    | tp ->
      expected_cof tp

  let meet tacs =
    function
    | D.TpCof ->
      let+ phis = MU.map (fun t -> t D.TpCof) tacs in
      S.Cof (Cof.Meet phis)
    | tp ->
      expected_cof tp

  let boundary tac = join [eq tac Dim.dim0; eq tac Dim.dim1]

  let assert_true vphi =
    EM.lift_cmp @@ CmpM.test_sequent [] vphi |>> function
    | true -> EM.ret ()
    | false ->
      EM.with_pp @@ fun ppenv ->
      let* tphi = EM.lift_qu @@ Qu.quote_cof vphi in
      EM.elab_err @@ Err.ExpectedTrue (ppenv, tphi)


  type branch_tac = T.chk_tac * (T.var -> T.bchk_tac)

  let rec gather_cofibrations (branches : branch_tac list) : (D.cof list * (T.var -> T.bchk_tac) list) m =
    match branches with
    | [] -> EM.ret ([], [])
    | (tac_phi, tac_tm) :: branches ->
      let* tphi = tac_phi D.TpCof in
      let* vphi = EM.lift_ev @@ Sem.eval_cof tphi in
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
    let* ttp = EM.lift_qu @@ Qu.quote_tp tp in
    let* _ = assert_true @@ Cof.join [phi0; phi1] in
    let* tm0 =
      T.abstract (D.TpPrf phi0) None @@ fun prf ->
      tac0 prf (tp, psi, psi_clo)
    in
    let+ tm1 =
      let* phi0_fn = EM.lift_ev @@ Sem.eval @@ S.Lam tm0 in
      let psi_fn = D.Lam psi_clo in
      let psi' = Cof.join [phi0; psi] in
      let* psi'_fn =
        EM.lift_cmp @@ Sem.splice_tm @@
        Splice.foreign_tp tp @@ fun tp ->
        Splice.foreign_cof phi0 @@ fun phi0 ->
        Splice.foreign_cof psi @@ fun psi ->
        Splice.foreign psi_fn @@ fun psi_fn ->
        Splice.foreign phi0_fn @@ fun phi0_fn ->
        Splice.term @@
        TB.lam @@ fun prf ->
        TB.cof_split tp phi0 (fun prf -> TB.ap phi0_fn [prf]) psi (fun prf -> TB.ap psi_fn [prf])
      in
      T.abstract (D.TpPrf phi1) None @@ fun prf ->
      tac1 prf (tp, psi', D.un_lam psi'_fn)
    and+ tphi0 = EM.lift_qu @@ Qu.quote_cof phi0
    and+ tphi1 = EM.lift_qu @@ Qu.quote_cof phi1 in
    S.CofSplit (ttp, tphi0, tphi1, tm0, tm1)



  let rec gather_cofibrations (branches : branch_tac list) : (D.cof list * (T.var -> T.bchk_tac) list) m =
    match branches with
    | [] -> EM.ret ([], [])
    | (tac_phi, tac_tm) :: branches ->
      let* tphi = tac_phi D.TpCof in
      let* vphi = EM.lift_ev @@ Sem.eval_cof tphi in
      let+ phis, tacs = gather_cofibrations branches in
      (vphi :: phis), tac_tm :: tacs

  let split (branches : branch_tac list) : T.bchk_tac =
    fun goal ->
    let* phis, tacs = gather_cofibrations branches in
    let disj_phi = Cof.join phis in
    let* _ = assert_true disj_phi in
    let rec go phis (tacs : (T.var -> T.bchk_tac) list) : T.bchk_tac =
      match phis, tacs with
      | [phi], [tac] ->
        split1 phi tac
      | phi :: phis, tac :: tacs ->
        split2 phi tac (Cof.join phis) (fun _ -> go phis tacs)
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
          let* tphi = EM.lift_qu @@ Qu.quote_cof phi in
          EM.elab_err @@ Err.ExpectedTrue (ppenv, tphi)
      end
    | tp, _, _ ->
      EM.expected_connective `Prf tp
end

module Pi =
struct
  let formation : (T.tp_tac, T.tp_tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.make @@
      let* base = T.Tp.run_virtual tac_base in
      let* vbase = EM.lift_ev @@ Sem.eval_tp base in
      let+ fam = T.abstract vbase nm @@ fun var -> T.Tp.run @@ tac_fam var in
      S.Pi (base, fam)

  let intro name (tac_body : T.var -> T.bchk_tac) : T.bchk_tac =
    function
    | D.Pi (base, fam), phi, phi_clo ->
      T.abstract base name @@ fun var ->
      let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam [T.Var.con var] in
      let+ tm = tac_body var (fib, phi, D.un_lam @@ D.compose (D.Lam (D.apply_to (T.Var.con var))) @@ D.Lam phi_clo) in
      S.Lam tm
    | tp, _, _ ->
      EM.expected_connective `Pi tp

  let apply tac_fun tac_arg : T.syn_tac =
    let* tfun, tp = tac_fun in
    let* base, fam = EM.dest_pi tp in
    let* targ = tac_arg base in
    let+ fib =
      let* varg = EM.lift_ev @@ Sem.eval targ in
      EM.lift_cmp @@ Sem.inst_tp_clo fam [varg]
    in
    S.Ap (tfun, targ), fib
end

module Sg =
struct
  let formation : (T.tp_tac, T.tp_tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.make @@
      let* base = T.Tp.run tac_base in
      let* vbase = EM.lift_ev @@ Sem.eval_tp base in
      let+ fam = T.abstract vbase nm @@ fun var -> T.Tp.run @@ tac_fam var in
      S.Sg (base, fam)

  let intro (tac_fst : T.bchk_tac) (tac_snd : T.bchk_tac) : T.bchk_tac =
    function
    | D.Sg (base, fam), phi, phi_clo ->
      let* tfst = tac_fst (base, phi, D.un_lam @@ D.compose D.fst @@ D.Lam phi_clo) in
      let+ tsnd =
        let* vfst = EM.lift_ev @@ Sem.eval tfst in
        let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam [vfst] in
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
      let* vfst = EM.lift_ev @@ Sem.eval @@ S.Fst tpair in
      let* _, fam = EM.dest_sg tp in
      EM.lift_cmp @@ Sem.inst_tp_clo fam [vfst]
    in
    S.Snd tpair, fib
end



module Univ =
struct
  let formation : T.tp_tac =
    T.Tp.make @@
    EM.ret S.Univ

  let univ_tac : T.chk_tac -> T.chk_tac =
    fun m ->
    function
    | D.Univ -> m D.Univ
    | tp ->
      EM.expected_connective `Univ tp

  let univ : T.chk_tac =
    univ_tac @@ fun _ ->
    EM.ret S.CodeUniv


  let nat : T.chk_tac =
    univ_tac @@ fun _ -> EM.ret S.CodeNat

  let quantifier tac_base tac_fam =
    fun univ ->
    let* base = tac_base univ in
    let* vbase = EM.lift_ev @@ Sem.eval base in
    let* famtp =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.foreign vbase @@ fun base ->
      Splice.foreign_tp univ @@ fun univ ->
      Splice.term @@ TB.pi (TB.el base) @@ fun _ -> univ
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
      Sem.splice_tp @@
      Splice.foreign_tp univ @@ fun univ ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      univ
    in
    let* fam = tac_fam piuniv in
    let* vfam = EM.lift_ev (Sem.eval fam) in
    let* bdry_tp =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.foreign_tp univ @@ fun univ ->
      Splice.foreign vfam @@ fun fam ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.boundary i)) @@ fun prf ->
      TB.el @@ TB.ap fam [i]
    in
    let* bdry = tac_bdry bdry_tp in
    EM.ret @@ S.CodePath (fam, bdry)

  let path_with_endpoints (tac_fam : T.chk_tac) (tac_a : T.bchk_tac) (tac_b : T.bchk_tac) : T.chk_tac =
    path tac_fam @@
    T.Chk.bchk @@
    Pi.intro None @@ fun i ->
    Pi.intro None @@ fun pf ->
    Cof.split
      [(Cof.eq (T.Chk.syn (T.Var.syn i)) Dim.dim0, fun _ -> tac_a);
       (Cof.eq (T.Chk.syn (T.Var.syn i)) Dim.dim1, fun _ -> tac_b)]

  let topc : T.syn_tac = EM.ret @@ (S.Cof (Cofibration.Meet []), D.TpCof)
  let botc : T.syn_tac = EM.ret @@ (S.Cof (Cofibration.Join []), D.TpCof)

  let coe tac_fam tac_src tac_trg tac_tm : T.syn_tac =
    let* piuniv =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.univ
    in
    let* fam = tac_fam piuniv in
    let* src = tac_src D.TpDim in
    let* trg = tac_trg D.TpDim in
    let* fam_src = EM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, src)) in
    let+ tm = tac_tm fam_src
    and+ fam_trg = EM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, trg)) in
    S.Coe (fam, src, trg, tm), fam_trg


  let hcom_bdy_tp tp r phi =
    EM.lift_cmp @@
    Sem.splice_tp @@
    Splice.foreign r @@ fun src ->
    Splice.foreign_cof phi @@ fun cof ->
    Splice.foreign_tp tp @@ fun vtp ->
    Splice.term @@
    TB.pi TB.tp_dim @@ fun i ->
    TB.pi (TB.tp_prf (TB.join [TB.eq i src; cof])) @@ fun _ ->
    vtp

  let hcom tac_code tac_src tac_trg tac_cof tac_tm : T.syn_tac =
    let* code = tac_code D.Univ in
    let* src = tac_src D.TpDim in
    let* trg = tac_trg D.TpDim in
    let* cof = tac_cof D.TpCof in
    let* vsrc = EM.lift_ev @@ Sem.eval src in
    let* vcof = EM.lift_ev @@ Sem.eval_cof cof in
    let* vtp = EM.lift_ev @@ Sem.eval_tp @@ S.El code in
    (* (i : dim) -> (_ : [i=src \/ cof]) -> A *)
    let+ tm = tac_tm @<< hcom_bdy_tp vtp vsrc vcof in
    S.HCom (code, src, trg, cof, tm), vtp

  let auto_hcom tac_code tac_src tac_trg tac_tm : T.bchk_tac =
    fun (vtp, vpsi, clo) ->
    let* code = tac_code D.Univ in
    let* elcode = EM.lift_ev @@ Sem.eval_tp @@ S.UnfoldEl code in
    let* () = EM.equate_tp vtp elcode in
    let* psi = EM.lift_qu @@ Qu.quote_cof vpsi in
    let* src = tac_src D.TpDim in
    let* trg = tac_trg D.TpDim in
    let* vsrc = EM.lift_ev @@ Sem.eval src in
    let* vtrg = EM.lift_ev @@ Sem.eval trg in
    let* tm =
      tac_tm @<<
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.foreign vsrc @@ fun src ->
      Splice.foreign vtrg @@ fun trg ->
      Splice.foreign_clo clo @@ fun pel ->
      Splice.foreign_cof vpsi @@ fun cof ->
      Splice.foreign_tp vtp @@ fun tp ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.join [TB.eq i src; cof])) @@ fun _ ->
      TB.sub tp (TB.meet [TB.eq i trg; cof]) @@ fun prf -> TB.ap pel [prf]
    in
    let* vtm = EM.lift_ev @@ Sem.eval tm in
    let* vtm' =
      EM.lift_cmp @@ Sem.splice_tm @@
      Splice.foreign vtm @@ fun tm ->
      Splice.term @@
      TB.lam @@ fun i ->
      TB.lam @@ fun prf ->
      TB.sub_out @@
      TB.ap tm [i; prf]
    in
    let* tm' =
      let* bdy_tp  = hcom_bdy_tp vtp vsrc vpsi in
      EM.lift_qu @@ Qu.quote_con bdy_tp vtm'
    in
    EM.ret @@ S.ElIn (S.HCom (code, src, trg, psi, tm'))

  let com tac_fam tac_src tac_trg tac_cof tac_tm : T.syn_tac =
    let* piuniv =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.univ
    in
    let* fam = tac_fam piuniv in
    let* src = tac_src D.TpDim in
    let* trg = tac_trg D.TpDim in
    let* cof = tac_cof D.TpCof in
    let* vfam = EM.lift_ev @@ Sem.eval fam in
    let* vsrc = EM.lift_ev @@ Sem.eval src in
    let* vcof = EM.lift_ev @@ Sem.eval_cof cof in
    (* (i : dim) -> (_ : [i=src \/ cof]) -> A i *)
    let+ tm =
      tac_tm @<<
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.foreign vfam @@ fun vfam ->
      Splice.foreign vsrc @@ fun src ->
      Splice.foreign_cof vcof @@ fun cof ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.join [TB.eq i src; cof])) @@ fun _ ->
      TB.el @@ TB.ap vfam [i]
    and+ vfam_trg = EM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, trg)) in
    S.Com (fam, src, trg, cof, tm), vfam_trg
end

module El =
struct
  let formation tac =
    T.Tp.make @@
    let+ tm = tac D.Univ in
    S.El tm

  let dest_el tp =
    match tp with
    | D.El con ->
      EM.lift_cmp @@ Sem.unfold_el con
    | _ ->
      EM.expected_connective `El tp

  let intro tac =
    fun (tp, phi, clo) ->
    let* unfolded = dest_el tp in
    let+ tm = tac (unfolded, phi, D.un_lam @@ D.compose D.el_out @@ D.Lam clo) in
    S.ElIn tm

  let elim tac =
    let* tm, tp = tac in
    let+ unfolded = dest_el tp in
    S.ElOut tm, unfolded
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
    fun goal ->
    let* tdef, tp_def = tac_def in
    let* vdef = EM.lift_ev @@ Sem.eval tdef in
    let* tbdy =
      let* const_vdef =
        EM.lift_cmp @@ Sem.splice_tm @@ Splice.foreign vdef @@ fun vdef ->
        Splice.term @@ TB.lam @@ fun _ -> vdef
      in
      T.abstract (D.Sub (tp_def, Cofibration.top, D.un_lam const_vdef)) nm_x @@ fun var ->
      tac_bdy var goal
    in
    EM.ret @@ S.Let (S.SubIn tdef, tbdy)
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

  let rec int_to_term =
    function
    | 0 -> S.Zero
    | n -> S.Suc (int_to_term (n - 1))

  let literal n : T.chk_tac =
    fun tp ->
    let+ () = assert_nat tp in
    int_to_term n

  let suc tac : T.chk_tac =
    fun tp ->
    let* () = assert_nat tp in
    let+ t = tac tp in
    S.Suc t

  let elim (tac_mot : T.chk_tac) (tac_case_zero : T.chk_tac) (tac_case_suc : T.chk_tac) tac_scrut : T.syn_tac =
    EM.push_problem "elim" @@
    let* tscrut, nattp = tac_scrut in
    let* () = assert_nat nattp in
    let* tmot =
      tac_mot @<<
      EM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.nat @@ fun _ -> TB.univ
    in
    let* vmot = EM.lift_ev @@ Sem.eval tmot in

    let* tcase_zero =
      let* code = EM.lift_cmp @@ Sem.do_ap vmot D.Zero in
      tac_case_zero @@ D.El code
    in

    let* tcase_suc =
      let* suc_tp =
        EM.lift_cmp @@ Sem.splice_tp @@
        Splice.foreign vmot @@ fun mot ->
        Splice.term @@
        TB.pi TB.nat @@ fun x ->
        TB.pi (TB.el (TB.ap mot [x])) @@ fun ih ->
        TB.el @@ TB.ap mot [TB.suc x]
      in
      tac_case_suc suc_tp
    in

    let+ fib_scrut =
      let* vscrut = EM.lift_ev @@ Sem.eval tscrut in
      EM.lift_cmp @@ Sem.do_ap vmot vscrut
    in

    S.NatElim (tmot, tcase_zero, tcase_suc, tscrut), D.El fib_scrut
end



module UnravelEl : sig
  (* Invariant: [unravel tp] produces an element of the universe when [tp] is a well-formed type, if it returns. *)
  val unravel_tp : D.tp -> T.chk_tac

end =
struct
  let ret_code : D.con -> T.chk_tac =
    fun code ->
      function
      | D.Univ ->
        EM.lift_qu @@ Qu.quote_con D.Univ code
      | tp ->
        EM.expected_connective `Univ tp

  let ret_tp : D.tp -> T.tp_tac =
    fun tp ->
    T.Tp.make @@
    EM.lift_qu @@ Qu.quote_tp tp

  (*    A type
   *    -----------
   *    unravel_tp A : univ
   *)
  let rec unravel_tp =
    function
    | D.El code ->
      ret_code code
    | D.Pi (base, fam) ->
      Univ.pi (unravel_tp base) (unravel_fam ~base fam)
    | D.Sg (base, fam) ->
      Univ.pi (unravel_tp base) (unravel_fam ~base fam)
    | _ -> failwith ""

  (*
   *     A type
   *     M : A
   *     ------------------------------
   *     unravel_iso_fwd A M : el(unravel_tp A)
   *)
  and unravel_iso_fwd : D.tp -> T.chk_tac -> T.chk_tac =
     fun tp tac ->
     match tp with
     | D.El _ ->
       tac

  (*
   *     A type
   *     x : A |- B(x) type
   *     M : (x : A) -> B(x)
   *     ------------------------------
   *     unravel_iso_fwd A M : el(unravel_tp((x : A) -> B(x)))
   *                     ... : el(∏(unravel_tp(A), λ x:unravel_tp(A). unravel_tp(B(bwd[A](x)))))
   *)
     | D.Pi (base, fam) as pitp ->
       T.Chk.bchk @@ El.intro @@
       (* (x : el(unravel_tp(A))) -> el(unravel_tp(B(bwd[A](x))) *)
       Pi.intro None @@ fun x ->
       let x' = unravel_iso_bwd base @@ T.Chk.syn @@ T.Var.syn x in
       let tacx' : T.Syn.tac = Pi.apply (T.Syn.ann tac (ret_tp pitp)) x' in (* tacx' : B(bwd[A](x)) *)
       T.BChk.chk @@ fun goal ->
       let* tx' = x' base in
       let* vx' = EM.lift_ev @@ Sem.eval tx' in
       let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam [vx'] in
       unravel_iso_fwd fib (T.Chk.syn tacx') goal

     | _ ->
       failwith ""

  (*
   *     A type
   *     M : el(unravel_tp A)
   *     ------------------------------
   *     unravel_iso_bwd A M : A
   *)
  and unravel_iso_bwd : D.tp -> T.chk_tac -> T.chk_tac =
    fun tp tac ->
    match tp with
    | D.El _ -> tac

    | D.Pi (base, fam) as pitp ->
  (*
   *     A type
   *     x : A |- B(x) type
   *
   *       M : el(unravel_tp((x : A) -> B(x)))
   *     ... : el(∏(unravel_tp(A), λ x:unravel_tp(A). unravel_tp(B(bwd[A](x)))))
   *     ------------------------------
   *     unravel_iso_bwd A M : (x : A) -> B(x)
   *)
      T.Chk.bchk @@
      Pi.intro None @@ fun x -> (* x : A *)
      let x' = unravel_iso_fwd base @@ T.Chk.syn @@ T.Var.syn x in (* x' : el(unravel_tp(A)) *)
      let tac' = El.elim @@ T.Syn.ann tac @@ El.formation @@ unravel_tp pitp in
      T.BChk.syn @@ Pi.apply tac' x'

    | _ -> failwith ""

  and unravel_fam : base:D.tp -> D.tp_clo -> T.chk_tac =
    fun ~base fam ->
    T.Chk.bchk @@ Pi.intro None @@ fun tac_var ->
    T.BChk.chk @@ fun goal ->
    let* x = unravel_iso_bwd base (T.Chk.syn (T.Var.syn tac_var)) base in
    let* vx = EM.lift_ev @@ Sem.eval x in
    let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam [vx] in
    unravel_tp fib goal
end

module Tactic =
struct
  let match_goal tac =
    fun goal ->
      let* tac = tac goal in
      tac goal

  let bmatch_goal = match_goal

  let elim_implicit_connectives : T.syn_tac -> T.syn_tac =
    fun tac ->
    let rec go (tm, tp) =
      match tp with
      | D.Sub (tp, _, _) ->
        go (S.SubOut tm, tp)
      | D.El code ->
        let* tp = EM.lift_cmp @@ Sem.unfold_el code in
        go (S.ElOut tm, tp)
      | _ ->
        EM.ret (tm, tp)
    in
    go @<< tac

  let rec intro_implicit_connectives : T.bchk_tac -> T.bchk_tac =
    fun tac ->
    match_goal @@ function
    | D.Sub _, _, _ ->
      EM.ret @@ Sub.intro @@ intro_implicit_connectives tac
    | D.El _, _, _ ->
      EM.ret @@ El.intro @@ intro_implicit_connectives tac
    | _ ->
      EM.ret tac



  let rec tac_lam name tac_body : T.bchk_tac =
    intro_implicit_connectives @@ Pi.intro name tac_body

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
      tac_multi_apply (elim_implicit_connectives @@ Pi.apply tac_fun tac) tacs

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

    let elim (mot : T.chk_tac) (cases : case_tac list) (scrut : T.syn_tac) : T.syn_tac =
      let* tscrut, ind_tp = scrut in
      let scrut = EM.ret (tscrut, ind_tp) in
      match ind_tp, mot with
      | D.Nat, mot ->
        let* tac_zero : T.chk_tac =
          match find_case "zero" cases with
          | Some ([], tac) -> EM.ret tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ T.Chk.bchk @@ Hole.unleash_hole (Some "zero") `Rigid
        in
        let* tac_suc =
          match find_case "suc" cases with
          | Some ([`Simple nm_z], tac) ->
            EM.ret @@ Pi.intro nm_z @@ fun _ -> Pi.intro None @@ fun _ -> T.BChk.chk tac
          | Some ([`Inductive (nm_z, nm_ih)], tac) ->
            EM.ret @@ Pi.intro nm_z @@ fun _ -> Pi.intro nm_ih @@ fun _ -> T.BChk.chk tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ Hole.unleash_hole (Some "suc") `Rigid
        in
        Nat.elim mot tac_zero (T.Chk.bchk tac_suc) scrut
      | _ ->
        EM.with_pp @@ fun ppenv ->
        let* tp = EM.lift_qu @@ Qu.quote_tp ind_tp in
        EM.elab_err @@ Err.CannotEliminate (ppenv, tp)

    let assert_simple_inductive =
      function
      | D.Nat ->
        EM.ret ()
      | tp ->
        EM.with_pp @@ fun ppenv ->
        let* tp = EM.lift_qu @@ Qu.quote_tp tp in
        EM.elab_err @@ Err.ExpectedSimpleInductive (ppenv, tp)

    let lam_elim cases : T.bchk_tac =
      match_goal @@ fun (tp, _, _) ->
      let* base, fam = EM.dest_pi tp in
      let mot_tac : T.chk_tac =
        T.Chk.bchk @@
        Pi.intro None @@ fun var ->
        T.BChk.chk @@ fun goal ->
        Format.eprintf "Before@.";
        let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam [T.Var.con var] in
        Format.eprintf "After@.";
        match fib with
        | D.El code ->
          EM.lift_qu @@ Qu.quote_con D.Univ code
        | _ -> failwith "lam_elim"
      in
      EM.ret @@
      Pi.intro None @@ fun x ->
      T.BChk.syn @@
      elim mot_tac cases @@
      El.elim @@ T.Var.syn x
  end
end
