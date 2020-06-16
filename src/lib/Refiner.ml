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

exception CJHM

open Basis
open Monads
open Monad.Notation (EM)
module MU = Monad.Util (EM)
open Bwd

type ('a, 'b) quantifier = 'a -> Ident.t * (T.var -> 'b) -> 'b

module GlobalUtil : sig
  val multi_pi : Env.cell list -> S.tp m -> S.tp m
  val multi_ap : Env.cell bwd -> D.cut -> D.cut
end =
struct
  let rec multi_pi (cells : Env.cell list) (finally : S.tp m) : S.tp m =
    match cells with
    | [] -> finally
    | cell :: cells ->
      let ctp, _ = Env.Cell.contents cell in
      let ident = Env.Cell.ident cell in
      let+ base = EM.quote_tp ctp
      and+ fam = EM.abstract ident ctp @@ fun _ -> multi_pi cells finally in
      S.Pi (base, ident, fam)

  let rec multi_ap (cells : Env.cell bwd) (finally : D.cut) : D.cut =
    match cells with
    | Emp -> finally
    | Snoc (cells, cell) ->
      let tp, con = Env.Cell.contents cell in
      multi_ap cells finally |> D.push @@ D.KAp (tp, con)
end


module Hole : sig
  val unleash_hole : string option -> [`Flex | `Rigid] -> T.Chk.tac
  val unleash_tp_hole : string option -> [`Flex | `Rigid] -> T.Tp.tac
  val unleash_syn_hole : string option -> [`Flex | `Rigid] -> T.Syn.tac
end =
struct
  let make_hole name flexity (tp, phi, clo) : D.cut m =
    let* env = EM.read in
    let cells = Env.locals env in

    EM.globally @@
    let* sym =
      let* tp = GlobalUtil.multi_pi (Bwd.to_list cells) @@ EM.quote_tp @@ D.GoalTp (name, D.Sub (tp, phi, clo)) in
      let* () =
        () |> EM.emit (ElabEnv.location env) @@ fun fmt () ->
        Format.fprintf fmt "Emitted hole:@,  @[<v>%a@]@." S.pp_sequent tp
      in
      let* vtp = EM.lift_ev @@ Sem.eval_tp tp in
      match flexity with
      | `Flex -> EM.add_flex_global vtp
      | `Rigid ->
        let ident =
          match name with
          | None -> `Anon
          | Some str -> `Machine ("?" ^ str)
        in
        EM.add_global ident vtp None
    in

    let cut = GlobalUtil.multi_ap cells (D.Global sym, []) in
    EM.ret (D.UnstableCut (D.push KGoalProj cut, D.KSubOut (phi, clo)), [])


  let unleash_hole name flexity : T.Chk.tac =
    T.Chk.brule @@ fun (tp, phi, clo) ->
    let* cut = make_hole name flexity (tp, phi, clo) in
    EM.quote_cut cut

  let unleash_tp_hole name flexity : T.Tp.tac =
    T.Tp.rule @@
    let* cut = make_hole name flexity @@ (D.Univ, Cubical.Cof.bot, D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp})) in
    EM.quote_tp @@ D.ElCut cut

  let unleash_syn_hole name flexity : T.Syn.tac =
    T.Syn.rule @@
    let* cut = make_hole name `Flex @@ (D.Univ, Cubical.Cof.bot, D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp})) in
    let tp = D.ElCut cut in
    let+ tm = tp |> T.Chk.run @@ unleash_hole name flexity in
    tm, tp
end


module Goal =
struct
  let formation lbl tac =
    T.Tp.rule @@
    let+ tp = T.Tp.run tac in
    S.GoalTp (lbl, tp)
end


module Sub =
struct
  let formation (tac_base : T.Tp.tac) (tac_phi : T.Chk.tac) (tac_tm : T.var -> T.Chk.tac) : T.Tp.tac =
    T.Tp.rule @@
    let* base = T.Tp.run tac_base in
    let* vbase = EM.lift_ev @@ Sem.eval_tp base in
    let* phi = T.Chk.run tac_phi D.TpCof in
    let+ tm =
      let* vphi = EM.lift_ev @@ Sem.eval_cof phi in
      T.abstract (D.TpPrf vphi) @@ fun prf ->
      vbase |> T.Chk.run @@ tac_tm prf
    in
    S.Sub (base, phi, tm)

  let intro (tac : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule @@
    function
    | D.Sub (tp_a, phi_a, clo_a), phi_sub, clo_sub ->
      let phi = Cubical.Cof.join [phi_a; phi_sub] in
      let* partial =
        EM.lift_cmp @@ Sem.splice_tm @@
        Splice.cof phi_a @@ fun phi_a ->
        Splice.cof phi_sub @@ fun phi_sub ->
        Splice.clo clo_a @@ fun fn_a ->
        Splice.clo clo_sub @@ fun fn_sub ->
        Splice.term @@ TB.lam @@ fun _ ->
        TB.cof_split
          [phi_a, TB.ap fn_a [TB.prf];
           phi_sub, TB.sub_out @@ TB.ap fn_sub [TB.prf]]
      in
      let+ tm = T.Chk.brun tac (tp_a, phi, D.un_lam partial) in
      S.SubIn tm
    | tp, _, _ ->
      EM.expected_connective `Sub tp

  let elim (tac : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* tm, subtp = T.Syn.run tac in
    match subtp with
    | D.Sub (tp, _, _) ->
      EM.ret (S.SubOut tm, tp)
    | tp ->
      EM.expected_connective `Sub tp
end

module Dim =
struct
  let formation : T.Tp.tac =
    T.Tp.virtual_rule @@
    EM.ret S.TpDim

  let dim0 : T.Chk.tac =
    T.Chk.rule @@
    function
    | D.TpDim ->
      EM.ret S.Dim0
    | tp ->
      EM.expected_connective `Dim tp

  let dim1 : T.Chk.tac =
    T.Chk.rule @@
    function
    | D.TpDim ->
      EM.ret S.Dim1
    | tp ->
      EM.expected_connective `Dim tp

  let literal : int -> T.Chk.tac =
    function
    | 0 -> dim0
    | 1 -> dim1
    | n ->
      T.Chk.rule @@ fun _ ->
      EM.elab_err @@ Err.ExpectedDimensionLiteral n
end

module Cof =
struct
  let formation : T.Tp.tac =
    T.Tp.virtual_rule @@
    EM.ret S.TpCof

  let expected_cof =
    EM.expected_connective `Cof

  let eq tac0 tac1 =
    T.Chk.rule @@
    function
    | D.TpCof ->
      let+ r0 = T.Chk.run tac0 D.TpDim
      and+ r1 = T.Chk.run tac1 D.TpDim in
      S.Cof (Cubical.Cof.Eq (r0, r1))
    | tp ->
      expected_cof tp

  let join tacs =
    T.Chk.rule @@
    function
    | D.TpCof ->
      let+ phis = MU.map (fun t -> T.Chk.run t D.TpCof) tacs in
      S.Cof (Cubical.Cof.Join phis)
    | tp ->
      expected_cof tp

  let meet tacs =
    T.Chk.rule @@
    function
    | D.TpCof ->
      let+ phis = MU.map (fun t -> T.Chk.run t D.TpCof) tacs in
      S.Cof (Cubical.Cof.Meet phis)
    | tp ->
      expected_cof tp

  let boundary tac = join [eq tac Dim.dim0; eq tac Dim.dim1]

  let assert_true vphi =
    EM.lift_cmp @@ CmpM.test_sequent [] vphi |>> function
    | true -> EM.ret ()
    | false ->
      EM.with_pp @@ fun ppenv ->
      let* tphi = EM.quote_cof vphi in
      EM.elab_err @@ Err.ExpectedTrue (ppenv, tphi)


  module Split : sig
    type branch_tac = {cof : T.Chk.tac; bdy : T.var -> T.Chk.tac}
    val split : branch_tac list -> T.Chk.tac
  end =
  struct
    type branch_tac = {cof : T.Chk.tac; bdy : T.var -> T.Chk.tac}
    type branch_tac' = {cof : D.cof; tcof : S.t; bdy : T.var -> T.Chk.tac}
    type branch = {cof : D.cof; tcof : S.t; fn : D.con; bdy : S.t}

    let rec gather_branches (branches : branch_tac list) : (D.cof * branch_tac' list) m =
      match branches with
      | [] -> EM.ret (Cubical.Cof.bot, [])
      | branch :: branches ->
        let* tphi = T.Chk.run branch.cof D.TpCof in
        let* vphi = EM.lift_ev @@ Sem.eval_cof tphi in
        let+ psi, tacs = gather_branches branches in
        Cubical.Cof.join [vphi; psi], {cof = vphi; tcof = tphi; bdy = branch.bdy} :: tacs


    let splice_split branches =
      let phis, fns = List.split branches in
      EM.lift_cmp @@ Sem.splice_tm @@
      Splice.cons (List.map D.cof_to_con phis) @@ fun phis ->
      Splice.cons fns @@ fun fns ->
      Splice.term @@ TB.lam @@ fun _ ->
      TB.cof_split @@ List.combine phis @@ List.map (fun fn -> TB.ap fn [TB.prf]) fns

    module State =
    struct
      open BwdNotation
      type t =
        {disj : D.cof;
         fns : (D.cof * D.con) bwd;
         acc : (S.t * S.t) bwd}

      let init : t =
        {disj = Cubical.Cof.bot;
         fns = Emp;
         acc = Emp}

      let append : t -> branch -> t =
        fun state branch ->
        {disj = Cubical.Cof.join [state.disj; branch.cof];
         fns = state.fns #< (branch.cof, branch.fn);
         acc = state.acc #< (branch.tcof, branch.bdy)}
    end

    let split (branches : branch_tac list) : T.Chk.tac =
      T.Chk.brule @@ fun (tp, psi, psi_clo) ->
      let* disjunction, tacs = gather_branches branches in
      let* () = assert_true disjunction in

      let step : State.t -> branch_tac' -> State.t m =
        fun state branch ->
        let* bdy =
          let psi' = Cubical.Cof.join [state.disj; psi] in
          let* psi'_fn = splice_split @@ (psi, D.Lam (`Anon, psi_clo)) :: Bwd.to_list state.fns in
          T.abstract (D.TpPrf branch.cof) @@ fun prf ->
          T.Chk.brun (branch.bdy prf) (tp, psi', D.un_lam psi'_fn)
        in
        let+ fn = EM.lift_ev @@ Sem.eval (S.Lam (`Anon, bdy)) in
        State.append state {cof = branch.cof; tcof = branch.tcof; fn; bdy}
      in

      let rec fold : State.t -> branch_tac' list -> S.t m =
        fun state ->
          function
          | [] ->
            EM.ret @@ S.CofSplit (Bwd.to_list state.acc)
          | tac :: tacs ->
            let* state = step state tac in
            fold state tacs
      in

      fold State.init tacs
  end

  include Split

end

module Prf =
struct
  let formation tac_phi =
    T.Tp.virtual_rule @@
    let+ phi = T.Chk.run tac_phi D.TpCof in
    S.TpPrf phi

  let intro =
    T.Chk.brule @@
    function
    | D.TpPrf phi, _, _ ->
      let+ () = Cof.assert_true phi in
      S.Prf
    | tp, _, _ ->
      EM.expected_connective `Prf tp
end

module Pi =
struct
  let formation : (T.Tp.tac, T.Tp.tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.rule @@
      let* base = T.Tp.run_virtual tac_base in
      let* vbase = EM.lift_ev @@ Sem.eval_tp base in
      let+ fam = T.abstract ~ident:nm vbase @@ fun var -> T.Tp.run @@ tac_fam var in
      S.Pi (base, nm, fam)

  let intro ?(ident = `Anon) (tac_body : T.var -> T.Chk.tac) : T.Chk.tac =
    T.Chk.brule @@
    function
    | D.Pi (base, _, fam), phi, phi_clo ->
      T.abstract ~ident base @@ fun var ->
      let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam @@ T.Var.con var in
      let+ tm = T.Chk.brun (tac_body var) (fib, phi, D.un_lam @@ D.compose (D.Lam (`Anon, D.apply_to (T.Var.con var))) @@ D.Lam (`Anon, phi_clo)) in
      S.Lam (ident, tm)
    | tp, _, _ ->
      EM.expected_connective `Pi tp

  let apply tac_fun tac_arg : T.Syn.tac =
    T.Syn.rule @@
    let* tfun, tp = T.Syn.run tac_fun in
    match tp with
    | D.Pi (base, _, fam) ->
      let* targ = T.Chk.run tac_arg base in
      let+ fib =
        let* varg = EM.lift_ev @@ Sem.eval targ in
        EM.lift_cmp @@ Sem.inst_tp_clo fam varg
      in
      S.Ap (tfun, targ), fib
    | _ ->
      Format.printf "Bad apply!! %a@." D.pp_tp tp;
      EM.expected_connective `Pi tp
end

module Sg =
struct
  let formation : (T.Tp.tac, T.Tp.tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.rule @@
      let* base = T.Tp.run tac_base in
      let* vbase = EM.lift_ev @@ Sem.eval_tp base in
      let+ fam = T.abstract ~ident:nm vbase @@ fun var -> T.Tp.run @@ tac_fam var in
      S.Sg (base, nm, fam)

  let intro (tac_fst : T.Chk.tac) (tac_snd : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule @@
    function
    | D.Sg (base, _, fam), phi, phi_clo ->
      let* tfst = T.Chk.brun tac_fst (base, phi, D.un_lam @@ D.compose D.fst @@ D.Lam (`Anon, phi_clo)) in
      let+ tsnd =
        let* vfst = EM.lift_ev @@ Sem.eval tfst in
        let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam vfst in
        T.Chk.brun tac_snd (fib, phi, D.un_lam @@ D.compose D.snd @@ D.Lam (`Anon, phi_clo))
      in
      S.Pair (tfst, tsnd)
    | tp , _, _ ->
      EM.expected_connective `Sg tp

  let pi1 tac : T.Syn.tac =
    T.Syn.rule @@
    let* tpair, tp = T.Syn.run tac in
    match tp with
    | D.Sg (base, _, _) ->
      EM.ret (S.Fst tpair, base)
    | _ ->
      EM.expected_connective `Sg tp


  let pi2 tac : T.Syn.tac =
    T.Syn.rule @@
    let* tpair, tp = T.Syn.run tac in
    match tp with
    | D.Sg (_, _, fam) ->
      let+ fib =
        let* vfst = EM.lift_ev @@ Sem.eval @@ S.Fst tpair in
        EM.lift_cmp @@ Sem.inst_tp_clo fam vfst
      in
      S.Snd tpair, fib
    | _ ->
      EM.expected_connective `Sg tp
end



module Univ =
struct
  let formation : T.Tp.tac =
    T.Tp.rule @@
    EM.ret S.Univ

  let univ_tac : (D.tp -> S.t EM.m) -> T.Chk.tac =
    fun m ->
    T.Chk.rule @@
    function
    | D.Univ -> m D.Univ
    | tp ->
      EM.expected_connective `Univ tp

  let univ : T.Chk.tac =
    univ_tac @@ fun _ ->
    EM.ret S.CodeUniv


  let nat : T.Chk.tac =
    univ_tac @@ fun _ -> EM.ret S.CodeNat

  let circle : T.Chk.tac =
    univ_tac @@ fun _ -> EM.ret S.CodeCircle

  let quantifier (tac_base : T.Chk.tac) (tac_fam : T.Chk.tac) =
    fun univ ->
    let* base = T.Chk.run tac_base univ in
    let* vbase = EM.lift_ev @@ Sem.eval base in
    let* famtp =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.con vbase @@ fun base ->
      Splice.tp univ @@ fun univ ->
      Splice.term @@ TB.pi (TB.el base) @@ fun _ -> univ
    in
    let+ fam = T.Chk.run tac_fam famtp in
    base, fam

  let pi tac_base tac_fam : T.Chk.tac =
    univ_tac @@ fun univ ->
    let+ tp, fam = quantifier tac_base tac_fam univ in
    S.CodePi (tp, fam)

  let sg tac_base tac_fam : T.Chk.tac =
    univ_tac @@ fun univ ->
    let+ tp, fam = quantifier tac_base tac_fam univ in
    S.CodeSg (tp, fam)


  let ext (n : int) (tac_fam : T.Chk.tac) (tac_cof : T.Chk.tac) (tac_bdry : T.Chk.tac) : T.Chk.tac =
    univ_tac @@ fun univ ->
    let* tcof =
      let* tp_cof_fam = EM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@ TB.cube n @@ fun _ -> TB.tp_cof in
      EM.globally @@ T.Chk.run tac_cof tp_cof_fam
    in
    let* cof = EM.lift_ev @@ EvM.drop_all_cons @@ Sem.eval tcof in
    let* tfam =
      let* tp_fam = EM.lift_cmp @@ Sem.splice_tp @@ Splice.tp univ @@ fun univ -> Splice.term @@ TB.cube n @@ fun _ -> univ in
      T.Chk.run tac_fam tp_fam
    in
    let+ tbdry =
      let* fam = EM.lift_ev @@ Sem.eval tfam in
      let* tp_bdry =
        EM.lift_cmp @@ Sem.splice_tp @@
        Splice.con cof @@ fun cof ->
        Splice.con fam @@ fun fam ->
        Splice.term @@
        TB.cube n @@ fun js ->
        TB.pi (TB.tp_prf @@ TB.ap cof js) @@ fun _ ->
        TB.el @@ TB.ap fam js
      in
      T.Chk.run tac_bdry tp_bdry
    in
    S.CodeExt (n, tfam, `Global tcof, tbdry)

  let code_v (tac_dim : T.Chk.tac) (tac_pcode: T.Chk.tac) (tac_code : T.Chk.tac) (tac_pequiv : T.Chk.tac) : T.Chk.tac =
    univ_tac @@ fun _univ ->
    let* r = T.Chk.run tac_dim D.TpDim in
    let* vr : D.dim =
      let* vr_con = EM.lift_ev @@ Sem.eval r in
      EM.lift_cmp @@ Sem.con_to_dim vr_con
    in
    let* pcode =
      let tp_pcode = D.Pi (D.TpPrf (Cubical.Cof.eq vr Cubical.Dim.Dim0), `Anon, D.const_tp_clo D.Univ) in
      T.Chk.run tac_pcode tp_pcode
    in
    let* code = T.Chk.run tac_code D.Univ in
    let+ pequiv =
      T.Chk.run tac_pequiv @<<
      let* vpcode = EM.lift_ev @@ Sem.eval pcode in
      let* vcode = EM.lift_ev @@ Sem.eval code in
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.Macro.tp_pequiv_in_v ~r:vr ~pcode:vpcode ~code:vcode
    in
    S.CodeV (r, pcode, code, pequiv)

  let coe (tac_fam : T.Chk.tac) (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* piuniv =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.term @@
      TB.pi TB.tp_dim @@ fun _i ->
      TB.univ
    in
    let* fam = T.Chk.run tac_fam piuniv in
    let* src = T.Chk.run tac_src D.TpDim in
    let* trg = T.Chk.run tac_trg D.TpDim in
    let* fam_src = EM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, src)) in
    let+ tm = T.Chk.run tac_tm fam_src
    and+ fam_trg = EM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, trg)) in
    S.Coe (fam, src, trg, tm), fam_trg


  let hcom_bdy_tp tp r phi =
    EM.lift_cmp @@
    Sem.splice_tp @@
    Splice.con r @@ fun src ->
    Splice.cof phi @@ fun cof ->
    Splice.tp tp @@ fun vtp ->
    Splice.term @@
    TB.pi TB.tp_dim @@ fun i ->
    TB.pi (TB.tp_prf (TB.join [TB.eq i src; cof])) @@ fun _ ->
    vtp

  let hcom (tac_code : T.Chk.tac) (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_cof : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* code = T.Chk.run tac_code D.Univ in
    let* src = T.Chk.run tac_src D.TpDim in
    let* trg = T.Chk.run tac_trg D.TpDim in
    let* cof = T.Chk.run tac_cof D.TpCof in
    let* vsrc = EM.lift_ev @@ Sem.eval src in
    let* vcof = EM.lift_ev @@ Sem.eval_cof cof in
    let* vtp = EM.lift_ev @@ Sem.eval_tp @@ S.El code in
    (* (i : dim) -> (_ : [i=src \/ cof]) -> A *)
    let+ tm = T.Chk.run tac_tm @<< hcom_bdy_tp vtp vsrc vcof in
    S.HCom (code, src, trg, cof, tm), vtp

  let com (tac_fam : T.Chk.tac) (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_cof : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* piuniv =
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.term @@
      TB.pi TB.tp_dim @@ fun _i ->
      TB.univ
    in
    let* fam = T.Chk.run tac_fam piuniv in
    let* src = T.Chk.run tac_src D.TpDim in
    let* trg = T.Chk.run tac_trg D.TpDim in
    let* cof = T.Chk.run tac_cof D.TpCof in
    let* vfam = EM.lift_ev @@ Sem.eval fam in
    let* vsrc = EM.lift_ev @@ Sem.eval src in
    let* vcof = EM.lift_ev @@ Sem.eval_cof cof in
    (* (i : dim) -> (_ : [i=src \/ cof]) -> A i *)
    let+ tm =
      T.Chk.run tac_tm @<<
      EM.lift_cmp @@
      Sem.splice_tp @@
      Splice.con vfam @@ fun vfam ->
      Splice.con vsrc @@ fun src ->
      Splice.cof vcof @@ fun cof ->
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
    T.Tp.rule @@
    let+ tm = T.Chk.run tac D.Univ in
    S.El tm

  let dest_el tp =
    match tp with
    | D.ElStable con ->
      EM.lift_cmp @@ Sem.unfold_el con
    | _ ->
      EM.expected_connective `El tp

  let intro tac =
    T.Chk.brule @@ fun (tp, phi, clo) ->
    let* unfolded = dest_el tp in
    let+ tm = T.Chk.brun tac (unfolded, phi, D.un_lam @@ D.compose D.el_out @@ D.Lam (`Anon, clo)) in
    S.ElIn tm

  let elim tac =
    T.Syn.rule @@
    let* tm, tp = T.Syn.run tac in
    let+ unfolded = dest_el tp in
    S.ElOut tm, unfolded
end


module ElV =
struct
  let intro (tac_part : T.Chk.tac) (tac_tot : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule @@
    function
    | D.ElUnstable (`V (r, pcode, code, pequiv)), phi, clo ->
      let* part =
        let* tp_part =
          EM.lift_cmp @@ Sem.splice_tp @@
          Splice.con pcode @@ fun pcode ->
          Splice.dim r @@ fun r ->
          Splice.term @@
          TB.pi (TB.tp_prf (TB.eq r TB.dim0)) @@ fun _ ->
          TB.el @@ TB.ap pcode [TB.prf]
        in
        let* bdry_fn =
          EM.lift_cmp @@ Sem.splice_tm @@
          Splice.clo clo @@ fun clo ->
          Splice.term @@
          TB.lam @@ fun _ ->
          TB.lam @@ fun _ ->
          TB.ap clo [TB.prf]
        in
        T.Chk.brun tac_part (tp_part, phi, D.un_lam bdry_fn)
      in
      let* tot =
        let* tp = EM.lift_cmp @@ Sem.do_el code in
        let* vpart = EM.lift_ev @@ Sem.eval part in
        let* bdry_fn =
          EM.lift_cmp @@ Sem.splice_tm @@
          Splice.cof phi @@ fun phi ->
          Splice.clo clo @@ fun clo ->
          Splice.con vpart @@ fun part ->
          Splice.dim r @@ fun r ->
          Splice.con pcode @@ fun pcode ->
          Splice.con code @@ fun code ->
          Splice.con pequiv @@ fun pequiv ->
          Splice.term @@
          TB.lam @@ fun _ -> (* [r=0 ∨ phi] *)
          TB.cof_split
            [TB.eq r TB.dim0, TB.ap (TB.Equiv.equiv_fwd (TB.ap pequiv [TB.prf])) [TB.ap part [TB.prf]];
             phi, TB.vproj r pcode code pequiv @@ TB.ap clo [TB.prf]]
        in
        T.Chk.brun tac_tot (tp, Cubical.Cof.join [Cubical.Cof.eq r Cubical.Dim.Dim0; phi], D.un_lam bdry_fn)
      in
      let* tr = EM.quote_dim r in
      let+ t_pequiv =
        let* tp_pequiv =
          EM.lift_cmp @@ Sem.splice_tp @@
          Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
        in
        EM.quote_con tp_pequiv pequiv
      in
      S.VIn (tr, t_pequiv, part, tot)
    | tp, _, _ ->
      EM.expected_connective `ElV tp

  let elim (tac_v : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* tm, tp = T.Syn.run tac_v in
    match tp with
    | D.ElUnstable (`V (r, pcode, code, pequiv)) ->
      let* tr = EM.quote_dim r in
      let* tpcode = EM.quote_con (D.Pi (D.TpPrf (Cubical.Cof.eq r Cubical.Dim.Dim0), `Anon, D.const_tp_clo D.Univ)) pcode in
      let* tcode = EM.quote_con D.Univ code in
      let* t_pequiv =
        let* tp_pequiv =
          EM.lift_cmp @@ Sem.splice_tp @@
          Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
        in
        EM.quote_con tp_pequiv pequiv
      in
      let vproj = S.VProj (tr, tpcode, tcode, t_pequiv, tm) in
      let* tp_vproj = EM.lift_cmp @@ Sem.do_el code in
      EM.ret (vproj, tp_vproj)
    | _ ->
      EM.expected_connective `ElV tp
end

module ElHCom =
struct
  let intro (tac_walls : T.Chk.tac) (tac_cap : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule @@
    function
    | D.ElUnstable (`HCom (r, r', phi, bdy)), psi, psi_clo ->
      let* twalls =
        let* tp_walls =
          EM.lift_cmp @@ Sem.splice_tp @@
          Splice.cof phi @@ fun phi ->
          Splice.con bdy @@ fun bdy ->
          Splice.dim r' @@ fun r' ->
          Splice.term @@ TB.pi (TB.tp_prf phi) @@ fun _ -> TB.el @@ TB.ap bdy [r'; TB.prf]
        in
        let* bdry_fn =
          EM.lift_cmp @@ Sem.splice_tm @@
          Splice.clo psi_clo @@ fun psi_clo ->
          Splice.term @@
          TB.lam @@ fun _ -> (* [psi] *)
          TB.lam @@ fun _ -> (* [phi] *)
          TB.ap psi_clo [TB.prf]
        in
        T.Chk.brun tac_walls (tp_walls, psi, D.un_lam bdry_fn)
      in
      let+ tcap =
        let* walls = EM.lift_ev @@ Sem.eval twalls in
        let* tp_cap =
          EM.lift_cmp @@ Sem.splice_tp @@
          Splice.con bdy @@ fun bdy ->
          Splice.dim r @@ fun r ->
          Splice.term @@ TB.el @@ TB.ap bdy [r; TB.prf]
        in
        let* bdry_fn =
          EM.lift_cmp @@ Sem.splice_tm @@
          Splice.dim r @@ fun r ->
          Splice.dim r' @@ fun r' ->
          Splice.cof phi @@ fun phi ->
          Splice.cof psi @@ fun psi ->
          Splice.clo psi_clo @@ fun psi_clo ->
          Splice.con walls @@ fun walls ->
          Splice.con bdy @@ fun bdy ->
          Splice.term @@
          TB.lam @@ fun _ -> (* [phi ∨ psi] *)
          TB.cof_split
            [psi, TB.cap r r' phi bdy @@ TB.ap psi_clo [TB.prf];
             phi, TB.coe (TB.lam ~ident:(`Machine "i") @@ fun i -> TB.ap bdy [i; TB.prf]) r' r (TB.ap walls [TB.prf])]
        in
        T.Chk.brun tac_cap (tp_cap, Cubical.Cof.join [phi; psi], D.un_lam bdry_fn)
      and+ tr = EM.quote_dim r
      and+ tr' = EM.quote_dim r'
      and+ tphi = EM.quote_cof phi in
      S.Box (tr, tr', tphi, twalls, tcap)

    | tp, _, _ ->
      EM.expected_connective `ElHCom tp

  let elim (tac_box : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* box, box_tp = T.Syn.run tac_box in
    match box_tp with
    | D.ElUnstable (`HCom (r, r', phi, bdy)) ->
      let+ tr = EM.quote_dim r
      and+ tr' = EM.quote_dim r'
      and+ tphi = EM.quote_cof phi
      and+ tbdy =
        let* tp_bdy = Univ.hcom_bdy_tp D.Univ (D.dim_to_con r) phi in
        EM.quote_con tp_bdy bdy
      and+ tp_cap =
        let* code_fib = EM.lift_cmp @@ Sem.do_ap2 bdy (D.dim_to_con r) D.Prf in
        EM.lift_cmp @@ Sem.do_el code_fib
      in
      S.Cap (tr, tr', tphi, tbdy, box), tp_cap
    | _ ->
      EM.expected_connective `ElHCom box_tp
end


module Structural =
struct


  let lookup_var id : T.Syn.tac =
    T.Syn.rule @@
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
    T.Syn.rule @@
    let* env = EM.read in
    let ix = ElabEnv.size env - lvl - 1 in
    index ix

  let generalize ident (tac : T.Chk.tac) : T.Chk.tac =
    let rec intros cells tac : T.Chk.tac =
      match cells with
      | [] ->
        tac
      | cell :: cells ->
        let ident = Env.Cell.ident cell in
        Pi.intro ~ident @@ fun _ ->
        intros cells tac
    in

    T.Chk.rule @@
    fun tp ->
      let* env = EM.read in
      let* lvl =
        EM.resolve ident |>>
        function
        | `Local ix -> EM.ret @@ ElabEnv.size env - ix - 1
        | _ -> EM.elab_err @@ Err.UnboundVariable ident
      in

      let cells = Env.locals env in
      let cells_fwd = Bwd.to_list cells in

      let* cut =
        EM.globally @@
        let* global_tp =
          let* tp = GlobalUtil.multi_pi cells_fwd @@ EM.quote_tp tp in
          EM.lift_ev @@ Sem.eval_tp tp
        in
        let* def =
          let prefix = ListUtil.take lvl cells_fwd in
          let* tm = global_tp |> T.Chk.run @@ intros prefix tac in
          EM.lift_ev @@ Sem.eval tm
        in
        let* sym = EM.add_global `Anon global_tp @@ Some def in
        EM.ret @@ GlobalUtil.multi_ap cells (D.Global sym, [])
      in
      EM.quote_cut cut



  let let_ ?(ident = `Anon) (tac_def : T.Syn.tac) (tac_bdy : T.var -> T.Chk.tac) : T.Chk.tac =
    T.Chk.brule @@ fun goal ->
    let* tdef, tp_def = T.Syn.run tac_def in
    let* vdef = EM.lift_ev @@ Sem.eval tdef in
    let* tbdy =
      let* const_vdef =
        EM.lift_cmp @@ Sem.splice_tm @@ Splice.con vdef @@ fun vdef ->
        Splice.term @@ TB.lam @@ fun _ -> vdef
      in
      T.abstract ~ident (D.Sub (tp_def, Cubical.Cof.top, D.un_lam const_vdef)) @@ fun var ->
      T.Chk.brun (tac_bdy var) goal
    in
    EM.ret @@ S.Let (S.SubIn tdef, ident, tbdy)

  let let_syn ?(ident = `Anon) (tac_def : T.Syn.tac) (tac_bdy : T.var -> T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    let* tdef, tp_def = T.Syn.run tac_def in
    let* vdef = EM.lift_ev @@ Sem.eval tdef in
    let* tbdy, tbdytp =
      let* const_vdef =
        EM.lift_cmp @@ Sem.splice_tm @@ Splice.con vdef @@ fun vdef ->
        Splice.term @@ TB.lam @@ fun _ -> vdef
      in
      T.abstract ~ident (D.Sub (tp_def, Cubical.Cof.top, D.un_lam const_vdef)) @@ fun var ->
      let* tbdy, bdytp = T.Syn.run @@ tac_bdy var in
      let* tbdytp = EM.quote_tp bdytp in
      EM.ret (tbdy, tbdytp)
    in
    let* bdytp = EM.lift_ev @@ EvM.append [D.SubIn vdef] @@ Sem.eval_tp tbdytp in
    EM.ret (S.Let (S.SubIn tdef, ident, tbdy), bdytp)
end


module Nat =
struct
  let formation =
    T.Tp.rule @@
    EM.ret S.Nat

  let assert_nat =
    function
    | D.Nat -> EM.ret ()
    | tp -> EM.expected_connective `Nat tp

  let rec int_to_term =
    function
    | 0 -> S.Zero
    | n -> S.Suc (int_to_term (n - 1))

  let literal n : T.Chk.tac =
    T.Chk.rule @@
    fun tp ->
    let+ () = assert_nat tp in
    int_to_term n

  let suc tac : T.Chk.tac =
    T.Chk.rule @@
    fun tp ->
    let* () = assert_nat tp in
    let+ t = T.Chk.run tac tp in
    S.Suc t

  let elim (tac_mot : T.Chk.tac) (tac_case_zero : T.Chk.tac) (tac_case_suc : T.Chk.tac) (tac_scrut : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    EM.push_problem "elim" @@
    let* tscrut, nattp = T.Syn.run tac_scrut in
    let* () = assert_nat nattp in let* tmot =
      T.Chk.run tac_mot @<<
      EM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.nat @@ fun _ -> TB.univ
    in
    let* vmot = EM.lift_ev @@ Sem.eval tmot in

    let* tcase_zero =
      let* code = EM.lift_cmp @@ Sem.do_ap vmot D.Zero in
      let* tp = EM.lift_cmp @@ Sem.do_el code in
      T.Chk.run tac_case_zero tp
    in

    let* tcase_suc =
      let* suc_tp =
        EM.lift_cmp @@ Sem.splice_tp @@
        Splice.con vmot @@ fun mot ->
        Splice.term @@
        TB.pi TB.nat @@ fun x ->
        TB.pi (TB.el (TB.ap mot [x])) @@ fun _ih ->
        TB.el @@ TB.ap mot [TB.suc x]
      in
      T.Chk.run tac_case_suc suc_tp
    in

    let+ fib_scrut =
      let* vscrut = EM.lift_ev @@ Sem.eval tscrut in
      let* code = EM.lift_cmp @@ Sem.do_ap vmot vscrut in
      EM.lift_cmp @@ Sem.do_el code
    in

    S.NatElim (tmot, tcase_zero, tcase_suc, tscrut), fib_scrut
end


module Circle =
struct
  let formation =
    T.Tp.rule @@
    EM.ret S.Circle

  let assert_circle =
    function
    | D.Circle -> EM.ret ()
    | tp -> EM.expected_connective `Circle tp

  let base =
    T.Chk.rule @@ fun tp ->
    let+ () = assert_circle tp in
    S.Base

  let loop tac : T.Chk.tac =
    T.Chk.rule @@ fun tp ->
    let* () = assert_circle tp in
    let+ r = T.Chk.run tac D.TpDim in
    S.Loop r

  let elim (tac_mot : T.Chk.tac) (tac_case_base : T.Chk.tac) (tac_case_loop : T.Chk.tac) (tac_scrut : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule @@
    EM.push_problem "elim" @@
    let* tscrut, circletp = T.Syn.run tac_scrut in
    let* () = assert_circle circletp in
    let* tmot =
      T.Chk.run tac_mot @<<
      EM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.circle @@ fun _ -> TB.univ
    in
    let* vmot = EM.lift_ev @@ Sem.eval tmot in

    let* tcase_base =
      let* code = EM.lift_cmp @@ Sem.do_ap vmot D.Base in
      let* tp = EM.lift_cmp @@ Sem.do_el code in
      T.Chk.run tac_case_base tp
    in

    let* tcase_loop =
      let* loop_tp =
        EM.lift_cmp @@ Sem.splice_tp @@
        Splice.con vmot @@ fun mot ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun x ->
        TB.el @@ TB.ap mot [TB.loop x]
      in
      T.Chk.run tac_case_loop loop_tp
    in

    let+ fib_scrut =
      let* vscrut = EM.lift_ev @@ Sem.eval tscrut in
      let* code = EM.lift_cmp @@ Sem.do_ap vmot vscrut in
      EM.lift_cmp @@ Sem.do_el code
    in

    S.CircleElim (tmot, tcase_base, tcase_loop, tscrut), fib_scrut
end


module Tactic =
struct
  let match_goal (tac : _ -> T.Chk.tac EM.m) : T.Chk.tac =
    T.Chk.brule @@
    fun goal ->
      let* tac = tac goal in
      T.Chk.brun tac goal

  let rec elim_implicit_connectives : T.Syn.tac -> T.Syn.tac =
    fun tac ->
    T.Syn.rule @@
    let* tm, tp = T.Syn.run @@ T.Syn.whnf ~style:`UnfoldAll tac in
    match tp with
    | D.Sub _ ->
      T.Syn.run @@ elim_implicit_connectives @@ Sub.elim @@ T.Syn.rule @@ EM.ret (tm, tp)
        (* The above code only makes sense because I know that the argument to Sub.elim will not be called under a further binder *)
    | D.ElStable _ ->
      T.Syn.run @@ elim_implicit_connectives @@ El.elim @@ T.Syn.rule @@ EM.ret (tm, tp)
    | _ ->
      EM.ret (tm, tp)

  let rec intro_implicit_connectives : T.Chk.tac -> T.Chk.tac =
    fun tac ->
    T.Chk.whnf ~style:`UnfoldAll @@
    match_goal @@ function
    | D.Sub _, _, _ ->
      EM.ret @@ Sub.intro @@ intro_implicit_connectives tac
    | D.ElStable _, _, _ ->
      EM.ret @@ El.intro @@ intro_implicit_connectives tac
    | _ ->
      EM.ret tac

  let rec intro_subtypes : T.Chk.tac -> T.Chk.tac =
    fun tac ->
    T.Chk.whnf ~style:`UnfoldNone @@
    match_goal @@ function
    | D.Sub _, _, _ ->
      EM.ret @@ Sub.intro @@ intro_subtypes tac
    | _ ->
      EM.ret tac

  let rec tac_nary_quantifier (quant : ('a, 'b) quantifier) cells body =
    match cells with
    | [] -> body
    | (nm, tac) :: cells ->
      quant tac (nm, fun _ -> tac_nary_quantifier quant cells body)

  module Elim =
  struct
    type case_tac = CS.pat * T.Chk.tac

    let rec find_case (lbl : string) (cases : case_tac list) : (CS.pat_arg list * T.Chk.tac) option =
      match cases with
      | (CS.Pat pat, tac) :: _ when pat.lbl = lbl ->
        Some (pat.args, tac)
      | _ :: cases ->
        find_case lbl cases
      | [] ->
        None

    let elim (mot : T.Chk.tac) (cases : case_tac list) (scrut : T.Syn.tac) : T.Syn.tac =
      T.Syn.rule @@
      let* tscrut, ind_tp = T.Syn.run scrut in
      let scrut = T.Syn.rule @@ EM.ret (tscrut, ind_tp) (* only makes sense because because I know 'scrut' won't be used under some binder *) in
      match ind_tp, mot with
      | D.Nat, mot ->
        let* tac_zero : T.Chk.tac =
          match find_case "zero" cases with
          | Some ([], tac) -> EM.ret tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ Hole.unleash_hole (Some "zero") `Rigid
        in
        let* tac_suc =
          match find_case "suc" cases with
          | Some ([`Simple nm_z], tac) ->
            EM.ret @@ Pi.intro ~ident:nm_z @@ fun _ -> Pi.intro @@ fun _ -> tac
          | Some ([`Inductive (nm_z, nm_ih)], tac) ->
            EM.ret @@ Pi.intro ~ident:nm_z @@ fun _ -> Pi.intro ~ident:nm_ih @@ fun _ -> tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ Hole.unleash_hole (Some "suc") `Rigid
        in
        T.Syn.run @@ Nat.elim mot tac_zero tac_suc scrut
      | D.Circle, mot ->
        let* tac_base : T.Chk.tac =
          match find_case "base" cases with
          | Some ([], tac) -> EM.ret tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ Hole.unleash_hole (Some "base") `Rigid
        in
        let* tac_loop =
          match find_case "loop" cases with
          | Some ([`Simple nm_x], tac) ->
            EM.ret @@ Pi.intro ~ident:nm_x @@ fun _ -> tac
          | Some _ -> EM.elab_err Err.MalformedCase
          | None -> EM.ret @@ Hole.unleash_hole (Some "loop") `Rigid
        in
        T.Syn.run @@ Circle.elim mot tac_base tac_loop scrut
      | _ ->
        EM.with_pp @@ fun ppenv ->
        let* tp = EM.quote_tp ind_tp in
        EM.elab_err @@ Err.CannotEliminate (ppenv, tp)

    let assert_simple_inductive =
      function
      | D.Nat ->
        EM.ret ()
      | D.Circle ->
        EM.ret ()
      | tp ->
        EM.with_pp @@ fun ppenv ->
        let* tp = EM.quote_tp tp in
        EM.elab_err @@ Err.ExpectedSimpleInductive (ppenv, tp)

    let lam_elim cases : T.Chk.tac =
      match_goal @@ fun (tp, _, _) ->
      match tp with
      | D.Pi (_, _, fam) ->
        let mot_tac : T.Chk.tac =
          Pi.intro @@ fun var -> (* of inductive type *)
          T.Chk.brule @@ fun _goal ->
          let* fib = EM.lift_cmp @@ Sem.inst_tp_clo fam @@ D.ElIn (T.Var.con var) in
          let* tfib = EM.quote_tp fib in
          match tfib with
          | S.El code ->
            EM.ret code
          | _ ->
            EM.expected_connective `El fib
        in
        EM.ret @@
        Pi.intro @@ fun x ->
        T.Chk.syn @@
        elim mot_tac cases @@
        El.elim @@ T.Var.syn x
      | _ ->
        EM.expected_connective `Pi tp
  end
end
