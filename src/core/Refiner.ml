open Containers

open Basis
open Monads
open Bwd
open Bwd.Infix

open CodeUnit

module D = Domain
module S = Syntax
module Env = RefineEnv
module Err = RefineError
module RM = RefineMonad
module RMU = Monad.Util (RM)
module T = Tactic
module Splice = Splice
module TB = TermBuilder
module Sem = Semantics
module Qu = Quote

open Monad.Notation (RM)
module MU = Monad.Util (RM)

exception CJHM


type ('a, 'b) quantifier = 'a -> Ident.t * (T.var -> 'b) -> 'b

type 'a telescope =
  | Bind of Ident.t * 'a * (T.var -> 'a telescope)
  | Done


module Probe : sig
  val probe_chk : string option -> T.Chk.tac -> T.Chk.tac
  val probe_boundary : T.Chk.tac -> T.Chk.tac -> T.Chk.tac
  val probe_syn : string option -> T.Syn.tac -> T.Syn.tac

  val probe_goal_chk : ((Ident.t * S.tp) list -> S.tp -> unit RM.m) -> T.Chk.tac -> T.Chk.tac
  val probe_goal_syn : ((Ident.t * S.tp) list -> S.tp -> unit RM.m) -> T.Syn.tac -> T.Syn.tac

  (** Run the first tactic, and if the boundary is not satisfied, run the second tactic family at the term produced by the first tactic. *)
  val try_with_boundary : T.Chk.tac -> (S.t -> T.Chk.tac) -> T.Chk.tac
end =
struct
  let probe_goal_chk k tac =
    T.Chk.brule ~name:"probe_goal_chk" @@ fun (tp, phi, clo) ->
    let* s = T.Chk.brun tac (tp, phi, clo) in
    let+ () =
      let* stp = RM.quote_tp @@ D.Sub (tp, phi, clo) in

      let* env = RM.read in
      let cells = Env.locals env in
      RM.globally @@
      let* ctx = RM.destruct_cells @@ BwdLabels.to_list cells in
      k ctx stp
    in
    s

  let probe_goal_syn k tac =
    T.Syn.rule ~name:"probe_goal_syn" @@
      let* s, tp = T.Syn.run tac in
      let+ () =
        let* stp = RM.quote_tp tp in
        let* env = RM.read in
        let cells = Env.locals env in
        RM.globally @@
        let* ctx = RM.destruct_cells @@ BwdLabels.to_list cells in
        k ctx stp
      in
      s, tp

  let probe_chk name tac =
    probe_goal_chk (RM.print_state name) tac

  let probe_syn name tac =
    probe_goal_syn (RM.print_state name) tac

  let probe_boundary probe tac =
    T.Chk.brule ~name:"probe_boundary" @@ fun (tp, phi, clo) ->
    let* probe_tm = T.Chk.run probe tp in
    let* () = RM.print_boundary probe_tm tp phi clo in
    T.Chk.brun tac (tp, phi, clo)

  let try_with_boundary tac backup =
    T.Chk.brule ~name:"try_with_boundary" @@ fun (tp, phi, tm_clo) ->
    let* tm = T.Chk.brun tac (tp, phi, tm_clo) in
    let* bdry_sat = RM.boundary_satisfied tm tp phi tm_clo in
    match bdry_sat with
    | `BdryUnsat -> T.Chk.brun (backup tm) (tp, phi, tm_clo)
    | `BdrySat -> RM.ret tm
end


module Hole : sig
  val silent_hole : string option -> T.Chk.tac
  val unleash_hole : string option -> T.Chk.tac
  val silent_syn_hole : string option -> T.Syn.tac
  val unleash_syn_hole : string option -> T.Syn.tac
end =
struct
  let assert_hole_possible tp =
    RM.lift_cmp @@ Sem.whnf_tp_ tp |>>
    function
    | D.TpDim | D.TpCof | D.TpPrf _ ->
      let* ttp = RM.quote_tp tp in
      RM.with_pp @@ fun ppenv ->
      RM.refine_err @@ Err.HoleNotPermitted (ppenv, ttp)
    | _ -> RM.ret ()

  let make_hole name (tp, phi, clo) : D.cut m =
    let* () = assert_hole_possible tp in
    let* env = RM.read in
    let cells = Env.locals env in

    RM.globally @@
    let* sym =
      let* tp = RM.multi_pi (BwdLabels.to_list cells) @@ RM.quote_tp @@ D.Sub (tp, phi, clo) in
      let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
      let ident =
        match name with
        | None -> Ident.anon
        | Some str -> Ident.machine @@ "?" ^ str
      in
      RM.add_global ~unfolder:None ~shadowing:true ident vtp
    in

    let* () = RM.add_hole (tp, phi, clo) in

    let cut = RM.multi_ap cells (D.Global sym, []) in
    RM.ret (D.UnstableCut (cut, D.KSubOut (phi, clo)), [])

  let silent_hole name : T.Chk.tac =
    T.Chk.brule ~name:"silent_hole" @@ fun (tp, phi, clo) ->
    let* cut = make_hole name (tp, phi, clo) in
    RM.quote_cut cut

  let unleash_hole name : T.Chk.tac =
    Probe.probe_chk name @@
    T.Chk.brule ~name:"unleash_hole" @@ fun (tp, phi, clo) ->
    let* cut = make_hole name (tp, phi, clo) in
    RM.quote_cut cut

  let silent_syn_hole name : T.Syn.tac =
    T.Syn.rule ~name:"silent_syn_hole" @@
      let* cut = make_hole name @@ (D.Univ, CofBuilder.bot, D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp})) in
      let tp = D.ElCut cut in
      let+ tm = tp |> T.Chk.run @@ unleash_hole name in
      tm, tp

  let unleash_syn_hole name : T.Syn.tac =
    Probe.probe_syn name @@
    T.Syn.rule ~name:"unleash_syn_hole" @@
      let* cut = make_hole name @@ (D.Univ, CofBuilder.bot, D.Clo (S.tm_abort, {tpenv = Emp; conenv = Emp})) in
      let tp = D.ElCut cut in
      let+ tm = tp |> T.Chk.run @@ unleash_hole name in
      tm, tp
end


module Sub =
struct
  let formation (tac_base : T.Tp.tac) (tac_phi : T.Chk.tac) (tac_tm : T.var -> T.Chk.tac) : T.Tp.tac =
    T.Tp.rule ~name:"Sub.formation" @@
      let* base = T.Tp.run tac_base in
      let* vbase = RM.lift_ev @@ Sem.eval_tp base in
      let* phi = T.Chk.run tac_phi D.TpCof in
      let+ tm =
        let* vphi = RM.lift_ev @@ Sem.eval_cof phi in
        T.abstract (D.TpPrf vphi) @@ fun prf ->
        vbase |> T.Chk.run @@ tac_tm prf
      in
      S.Sub (base, phi, tm)

  let intro (tac : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"Sub.intro" @@
    function
    | D.Sub (tp_a, phi_a, clo_a), phi_sub, clo_sub ->
      let phi = CofBuilder.join [phi_a; phi_sub] in
      let* partial =
        RM.lift_cmp @@ Sem.splice_tm @@
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
      RM.expected_connective `Sub tp

  let elim (tac : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Sub.elim" @@
      let* tm, subtp = T.Syn.run tac in
      match subtp with
      | D.Sub (tp, _, _) ->
        RM.ret (S.SubOut tm, tp)
      | tp ->
        RM.expected_connective `Sub tp
end

module Dim =
struct
  let formation : T.Tp.tac =
    T.Tp.virtual_rule ~name:"Dim.formation" @@
    RM.ret S.TpDim

  let dim0 : T.Chk.tac =
    T.Chk.rule ~name:"Dim.dim0" @@
      function
      | D.TpDim ->
        RM.ret S.Dim0
      | tp ->
        RM.expected_connective `Dim tp

  let dim1 : T.Chk.tac =
    T.Chk.rule ~name:"Dim.dim1" @@
      function
      | D.TpDim ->
        RM.ret S.Dim1
      | tp ->
        RM.expected_connective `Dim tp

  let literal : int -> T.Chk.tac =
    function
    | 0 -> dim0
    | 1 -> dim1
    | n ->
      T.Chk.rule ~name:"Dim.literal" @@ fun _ ->
        RM.refine_err @@ Err.ExpectedDimensionLiteral n
end

module Cof =
struct
  let formation : T.Tp.tac =
    T.Tp.virtual_rule ~name:"Cof.formation" @@
    RM.ret S.TpCof

  let expected_cof =
    RM.expected_connective `Cof

  let eq tac0 tac1 =
    T.Chk.rule ~name:"Cof.eq" @@
      function
      | D.TpCof ->
        let+ r0 = T.Chk.run tac0 D.TpDim
        and+ r1 = T.Chk.run tac1 D.TpDim in
        S.CofBuilder.eq r0 r1
      | tp ->
        expected_cof tp

  let le tac0 tac1 =
    T.Chk.rule ~name:"Cof.le" @@
      function
      | D.TpCof ->
        let+ r0 = T.Chk.run tac0 D.TpDim
        and+ r1 = T.Chk.run tac1 D.TpDim in
        S.CofBuilder.le r0 r1
      | tp ->
        expected_cof tp


  let join tacs =
    T.Chk.rule ~name:"Cof.join" @@
      function
      | D.TpCof ->
        let+ phis = MU.map (fun t -> T.Chk.run t D.TpCof) tacs in
        S.CofBuilder.join phis
      | tp ->
        expected_cof tp

  let meet tacs =
    T.Chk.rule ~name:"Cof.meet" @@
      function
      | D.TpCof ->
        let+ phis = MU.map (fun t -> T.Chk.run t D.TpCof) tacs in
        S.CofBuilder.meet phis
      | tp ->
        expected_cof tp

  let boundary tac = join [eq tac Dim.dim0; eq tac Dim.dim1]

  let assert_true vphi =
    RM.lift_cmp @@ CmpM.test_sequent [] vphi |>> function
    | true -> RM.ret ()
    | false ->
      RM.with_pp @@ fun ppenv ->
      let* tphi = RM.quote_cof vphi in
      RM.refine_err @@ Err.ExpectedTrue (ppenv, tphi)


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
      | [] -> RM.ret (CofBuilder.bot, [])
      | branch :: branches ->
        let* tphi = T.Chk.run branch.cof D.TpCof in
        let* vphi = RM.lift_ev @@ Sem.eval_cof tphi in
        let+ psi, tacs = gather_branches branches in
        CofBuilder.join [vphi; psi], {cof = vphi; tcof = tphi; bdy = branch.bdy} :: tacs


    let splice_split branches =
      let phis, fns = List.split branches in
      RM.lift_cmp @@ Sem.splice_tm @@
      Splice.cons (List.map D.cof_to_con phis) @@ fun phis ->
      Splice.cons fns @@ fun fns ->
      Splice.term @@ TB.lam @@ fun _ ->
      TB.cof_split @@ List.combine phis @@ List.map (fun fn -> TB.ap fn [TB.prf]) fns

    module State =
    struct
      open Bwd.Infix
      type t =
        {disj : D.cof;
         fns : (D.cof * D.con) bwd;
         acc : (S.t * S.t) bwd}

      let init : t =
        {disj = CofBuilder.bot;
         fns = Emp;
         acc = Emp}

      let append : t -> branch -> t =
        fun state branch ->
        {disj = CofBuilder.join [state.disj; branch.cof];
         fns = state.fns #< (branch.cof, branch.fn);
         acc = state.acc #< (branch.tcof, branch.bdy)}
    end

    let split (branches : branch_tac list) : T.Chk.tac =
      T.Chk.brule ~name:"Split.split" @@ fun (tp, psi, psi_clo) ->
      let* disjunction, tacs = gather_branches branches in
      let* () = assert_true disjunction in

      let step : State.t -> branch_tac' -> State.t m =
        fun state branch ->
          let* bdy =
            let psi' = CofBuilder.join [state.disj; psi] in
            let* psi'_fn = splice_split @@ (psi, D.Lam (Ident.anon, psi_clo)) :: BwdLabels.to_list state.fns in
            T.abstract (D.TpPrf branch.cof) @@ fun prf ->
            T.Chk.brun (branch.bdy prf) (tp, psi', D.un_lam psi'_fn)
          in
          let+ fn = RM.lift_ev @@ Sem.eval (S.Lam (Ident.anon, bdy)) in
          State.append state {cof = branch.cof; tcof = branch.tcof; fn; bdy}
      in

      let rec fold : State.t -> branch_tac' list -> S.t m =
        fun state ->
          function
          | [] ->
            RM.ret @@ S.CofSplit (BwdLabels.to_list state.acc)
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
    T.Tp.virtual_rule ~name:"Prf.formation" @@
    let+ phi = T.Chk.run tac_phi D.TpCof in
    S.TpPrf phi

  let intro =
    T.Chk.brule ~name:"Prf.intro" @@
    function
    | D.TpPrf phi, _, _ ->
      let+ () = Cof.assert_true phi in
      S.Prf
    | tp, _, _ ->
      RM.expected_connective `Prf tp
end

module Pi =
struct
  let formation : (T.Tp.tac, T.Tp.tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.rule ~name:"Pi.formation" @@
        let* base = T.Tp.run_virtual tac_base in
        let* vbase = RM.lift_ev @@ Sem.eval_tp base in
        let+ fam = T.abstract ~ident:nm vbase @@ fun var -> T.Tp.run @@ tac_fam var in
        S.Pi (base, nm, fam)

  let intro ?(ident = Ident.anon) (tac_body : T.var -> T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"Pi.intro" @@
    function
    | D.Pi (base, _, fam), phi, phi_clo ->
      T.abstract ~ident base @@ fun var ->
      let* fib = RM.lift_cmp @@ Sem.inst_tp_clo fam @@ T.Var.con var in
      let+ tm = T.Chk.brun (tac_body var) (fib, phi, D.un_lam @@ D.compose (D.Lam (Ident.anon, D.apply_to (T.Var.con var))) @@ D.Lam (Ident.anon, phi_clo)) in
      S.Lam (ident, tm)
    | tp, _, _ ->
      RM.expected_connective `Pi tp

  let apply tac_fun tac_arg : T.Syn.tac =
    T.Syn.rule ~name:"Pi.apply" @@
      let* tfun, tp = T.Syn.run tac_fun in
      match tp with
      | D.Pi (base, _, fam) ->
        let* targ = T.Chk.run tac_arg base in
        let+ fib =
          let* varg = RM.lift_ev @@ Sem.eval targ in
          RM.lift_cmp @@ Sem.inst_tp_clo fam varg
        in
        S.Ap (tfun, targ), fib
      | _ ->
        Format.printf "Bad apply!! %a@." D.pp_tp tp;
        RM.expected_connective `Pi tp
end

module Sg =
struct
  let formation : (T.Tp.tac, T.Tp.tac) quantifier =
    fun tac_base (nm, tac_fam) ->
      T.Tp.rule ~name:"Sg.formation" @@
        let* base = T.Tp.run tac_base in
        let* vbase = RM.lift_ev @@ Sem.eval_tp base in
        let+ fam = T.abstract ~ident:nm vbase @@ fun var -> T.Tp.run @@ tac_fam var in
        S.Sg (base, nm, fam)

  let intro (tac_fst : T.Chk.tac) (tac_snd : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"Sg.intro" @@
    function
    | D.Sg (base, _, fam), phi, phi_clo ->
      let* tfst = T.Chk.brun tac_fst (base, phi, D.un_lam @@ D.compose D.fst @@ D.Lam (Ident.anon, phi_clo)) in
      let+ tsnd =
        let* vfst = RM.lift_ev @@ Sem.eval tfst in
        let* fib = RM.lift_cmp @@ Sem.inst_tp_clo fam vfst in
        T.Chk.brun tac_snd (fib, phi, D.un_lam @@ D.compose D.snd @@ D.Lam (Ident.anon, phi_clo))
      in
      S.Pair (tfst, tsnd)
    | tp , _, _ ->
      RM.expected_connective `Sg tp

  let pi1 tac : T.Syn.tac =
    T.Syn.rule ~name:"Sg.pi1" @@
      let* tpair, tp = T.Syn.run tac in
      match tp with
      | D.Sg (base, _, _) ->
        RM.ret (S.Fst tpair, base)
      | _ ->
        RM.expected_connective `Sg tp


  let pi2 tac : T.Syn.tac =
    T.Syn.rule ~name:"Sg.pi2" @@
      let* tpair, tp = T.Syn.run tac in
      match tp with
      | D.Sg (_, _, fam) ->
        let+ fib =
          let* vfst = RM.lift_ev @@ Sem.eval @@ S.Fst tpair in
          RM.lift_cmp @@ Sem.inst_tp_clo fam vfst
        in
        S.Snd tpair, fib
      | _ ->
        RM.expected_connective `Sg tp
end

module Univ =
struct
  let formation : T.Tp.tac =
    T.Tp.rule ~name:"Univ.formation" @@
      RM.ret S.Univ

  let univ_tac : string -> (D.tp -> S.t RM.m) -> T.Chk.tac =
    fun nm m ->
    T.Chk.rule ~name:nm @@
      function
      | D.Univ -> m D.Univ
      | tp ->
        RM.expected_connective `Univ tp

  let univ : T.Chk.tac =
    univ_tac "Univ.univ" @@ fun _ ->
    RM.ret S.CodeUniv


  let nat : T.Chk.tac =
    univ_tac "Univ.nat" @@ fun _ -> RM.ret S.CodeNat

  let circle : T.Chk.tac =
    univ_tac "Univ.circle" @@ fun _ -> RM.ret S.CodeCircle

  let quantifier (tac_base : T.Chk.tac) (tac_fam : T.Chk.tac) =
    fun univ ->
    let* base = T.Chk.run tac_base univ in
    let* vbase = RM.lift_ev @@ Sem.eval base in
    let* famtp =
      RM.lift_cmp @@
      Sem.splice_tp @@
      Splice.con vbase @@ fun base ->
      Splice.tp univ @@ fun univ ->
      Splice.term @@ TB.pi (TB.el base) @@ fun _ -> univ
    in
    let+ fam = T.Chk.run tac_fam famtp in
    base, fam

  let pi tac_base tac_fam : T.Chk.tac =
    univ_tac "Univ.pi" @@ fun univ ->
    let+ tp, fam = quantifier tac_base tac_fam univ in
    S.CodePi (tp, fam)

  let sg tac_base tac_fam : T.Chk.tac =
    univ_tac "Univ.sg" @@ fun univ ->
    let+ tp, fam = quantifier tac_base tac_fam univ in
    S.CodeSg (tp, fam)

  (* Quote a domain code signature to a syntax code signature, while optionally patching/renaming its fields
     [patch_tacs] is a function from fields to an optional tactic that will definitionally constrain the value of that field.
        `Patch will make the field an extension type, while `Subst will simply drop the field after instantiating it to the patch
     [renaming] is a function from fields to an optional new name for that field
  *)
  let quote_kan_tele_hooks
      (tele : D.kan_tele)
      ~(patch_tacs : Ident.t -> [`Patch of T.Chk.tac | `Subst of T.Chk.tac] option)
      ~(renaming : Ident.t -> Ident.t option)
      (univ : D.tp) : _ m =
    let rec go = function
      | D.KEmpty -> RM.ret S.KEmpty
      | D.KCell (lbl, code, tele) ->
        let lbl = Option.value ~default:lbl (renaming lbl) in
        match patch_tacs lbl with
        | Some (`Subst tac) ->
          let* tp = RM.lift_cmp @@ Sem.do_el code in
          let* patch = T.Chk.run tac tp in
          let* vpatch = RM.eval patch in
          RM.lift_cmp @@ Sem.inst_kan_tele_clo tele vpatch |>> go
        | Some (`Patch tac) ->
          let* tp = RM.lift_cmp @@ Sem.do_el code in
          let* patch = T.Chk.run tac tp in
          let* vpatch = RM.eval patch in
          let* patched_code =
            RM.lift_cmp @@
            Sem.splice_tm @@
            Splice.con code @@ fun code ->
            Splice.con vpatch @@ fun patch ->
            Splice.term @@
            TB.code_ext 0 code TB.top @@ TB.lam @@ fun _ -> patch
          in
          let* patched_tp = RM.lift_cmp @@ Sem.do_el patched_code in
          let* qpatched_code = RM.quote_con univ patched_code in
          RM.abstract (lbl :> Ident.t) patched_tp @@ fun _ ->
          let* tele = RM.lift_cmp @@ Sem.inst_kan_tele_clo tele vpatch in
          let+ qtele = go tele in
          S.KCell (lbl, qpatched_code, qtele)
        | None ->
          let* qcode = RM.quote_con univ code in
          let* tp = RM.lift_cmp @@ Sem.do_el code in
          RM.abstract (lbl :> Ident.t) tp @@ fun x ->
          let+ qtele = RM.lift_cmp @@ Sem.inst_kan_tele_clo tele x |>> go in
          S.KCell (lbl, qcode, qtele)
    in
    go tele

  let quote_kan_tele sign univ = quote_kan_tele_hooks sign ~patch_tacs:(fun _ -> None) ~renaming:(fun _ -> None) univ
  let patch_fields sign patch_tacs univ = quote_kan_tele_hooks sign ~patch_tacs ~renaming:(fun _ -> None) univ

  let rename_kan_tele sign renaming univ = quote_kan_tele_hooks sign ~renaming ~patch_tacs:(fun _ -> None) univ

  (** Abstract over all the variables in a code signature *)
  let abstract_kan_tele sign k =
    let rec go vars = function
      | D.KEmpty -> k (Bwd.to_list vars)
      | D.KCell (lbl, code, tele) ->
        let* tp = RM.lift_cmp @@ Sem.do_el code in
        RM.abstract lbl tp @@ fun x ->
        let* sign = RM.lift_cmp @@ Sem.inst_kan_tele_clo tele x in
        go (vars #< x) sign
    in
    go Emp sign

  let signature (tacs : [`Field of (Ident.t * T.Chk.tac) | `Include of T.Chk.tac * (Ident.t -> Ident.t option)] list) : T.Chk.tac =
    univ_tac "Univ.signature" @@ fun univ ->
    let rec go = function
      | [] -> RM.ret S.KEmpty
      | `Field (lbl,tac) :: tacs ->
        let* code = T.Chk.run tac univ in
        let* vcode = RM.lift_ev @@ Sem.eval code in
        let* tp = RM.lift_cmp @@ Sem.do_el vcode in
        RM.abstract (lbl :> Ident.t) tp @@ fun _ ->
        let+ tele = go tacs in
        S.KCell (lbl, code, tele)
      | `Include (tac, renaming) :: tacs ->
        let* inc = T.Chk.run tac univ in
        let* vinc = RM.eval inc in
        RM.lift_cmp @@ Sem.whnf_con_ vinc |>> function
        | D.StableCode (`Signature inc_tele) ->
          let* qinc_tele = rename_kan_tele inc_tele renaming univ in
          abstract_kan_tele inc_tele @@ fun _ ->
          let+ tele = go tacs in
          S.append_kan_tele qinc_tele tele
        | _ ->
          RM.with_pp @@ fun ppenv ->
          RM.refine_err @@
          Err.ExpectedSignature (ppenv, inc)
    in
    let+ tele = go tacs in
    S.CodeSignature tele

  let patch (sig_tac : T.Chk.tac) (tacs : Ident.t -> [`Patch of T.Chk.tac | `Subst of T.Chk.tac] option) : T.Chk.tac =
    univ_tac "Univ.patch" @@ fun univ ->
    let* code = T.Chk.run sig_tac univ in
    let* vcode = RM.lift_ev @@ Sem.eval code in
    let* tp = RM.lift_cmp @@ Sem.do_el vcode in
    let* whnf_tp = RM.lift_cmp @@ Sem.whnf_tp_ tp in
    match whnf_tp with
    | D.ElStable (`Signature sign) ->
      let+ sign = patch_fields sign tacs univ in
      S.CodeSignature sign
    | _ ->
      RM.expected_connective `Signature whnf_tp

  let total (vtele : D.kan_tele) (vfam : D.con) : T.Chk.tac =
    univ_tac "Univ.total" @@ fun univ ->
    let* qtele = quote_kan_tele vtele univ in
    abstract_kan_tele vtele @@ fun vars ->
    Debug.print "Taking total space of family: %a@." D.pp_con vfam;
    let lbls = D.kan_tele_lbls vtele in
    let strct = D.Struct (D.Fields (List.combine lbls vars)) in
    let* fib =
      RM.lift_cmp @@ Sem.splice_tm @@
      Splice.con vfam @@ fun fam ->
      Splice.con strct @@ fun strct ->
      Splice.term @@
      TB.el_out @@ TB.ap fam [TB.el_in strct]
    in
    let+ qfib = RM.quote_con D.Univ fib in
    S.CodeSignature (S.append_kan_tele qtele (S.KCell (`User ["fib"], qfib, S.KEmpty)))

  let ext (n : int) (tac_fam : T.Chk.tac) (tac_cof : T.Chk.tac) (tac_bdry : T.Chk.tac) : T.Chk.tac =
    univ_tac "Univ.ext" @@ fun univ ->
    let* tcof =
      let* tp_cof_fam = RM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@ TB.cube n @@ fun _ -> TB.tp_cof in
      RM.globally @@ T.Chk.run tac_cof tp_cof_fam
    in
    let* cof = RM.lift_ev @@ EvM.drop_all_cons @@ Sem.eval tcof in
    let* tfam =
      let* tp_fam = RM.lift_cmp @@ Sem.splice_tp @@ Splice.tp univ @@ fun univ -> Splice.term @@ TB.cube n @@ fun _ -> univ in
      T.Chk.run tac_fam tp_fam
    in
    let+ tbdry =
      let* fam = RM.lift_ev @@ Sem.eval tfam in
      let* tp_bdry =
        RM.lift_cmp @@ Sem.splice_tp @@
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


  let is_nullary_ext = function
    | D.ElStable (`Ext (0,_ ,`Global (Cof cof), _)) ->
      let* cof = RM.lift_cmp @@ Sem.cof_con_to_cof cof in
      RM.lift_cmp @@ CmpM.test_sequent [] cof
    | _ -> RM.ret false

  let infer_nullary_ext : T.Chk.tac =
    T.Chk.rule ~name:"Univ.infer_nullary_ext" @@ function
      | ElStable (`Ext (0,code ,`Global (Cof cof),bdry)) ->
        let* cof = RM.lift_cmp @@ Sem.cof_con_to_cof cof in
        let* () = Cof.assert_true cof in
        let* tp = RM.lift_cmp @@
          Sem.splice_tp @@
          Splice.con code @@ fun code ->
          Splice.term @@ TB.el code
        in
        let* tm = RM.lift_cmp @@
          Sem.splice_tm @@
          Splice.con bdry @@ fun bdry ->
          Splice.term @@
          TB.ap bdry [TB.prf]
        in
        let+ ttm = RM.lift_qu @@ Qu.quote_con tp tm in
        S.ElIn (S.SubIn ttm)
      | tp -> RM.expected_connective `ElExt tp

  let code_v (tac_dim : T.Chk.tac) (tac_pcode: T.Chk.tac) (tac_code : T.Chk.tac) (tac_pequiv : T.Chk.tac) : T.Chk.tac =
    univ_tac "Univ.code_v" @@ fun _univ ->
    let* r = T.Chk.run tac_dim D.TpDim in
    let* vr : D.dim =
      let* vr_con = RM.lift_ev @@ Sem.eval r in
      RM.lift_cmp @@ Sem.con_to_dim vr_con
    in
    let* pcode =
      let tp_pcode = D.Pi (D.TpPrf (CofBuilder.eq0 vr), Ident.anon, D.const_tp_clo D.Univ) in
      T.Chk.run tac_pcode tp_pcode
    in
    let* code = T.Chk.run tac_code D.Univ in
    let+ pequiv =
      T.Chk.run tac_pequiv @<<
      let* vpcode = RM.lift_ev @@ Sem.eval pcode in
      let* vcode = RM.lift_ev @@ Sem.eval code in
      RM.lift_cmp @@
      Sem.splice_tp @@
      Splice.Macro.tp_pequiv_in_v ~r:vr ~pcode:vpcode ~code:vcode
    in
    S.CodeV (r, pcode, code, pequiv)

  let coe (tac_fam : T.Chk.tac) (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Univ.coe" @@
      let* piuniv =
        RM.lift_cmp @@
        Sem.splice_tp @@
        Splice.term @@
        TB.pi TB.tp_dim @@ fun _i ->
        TB.univ
      in
      let* fam = T.Chk.run tac_fam piuniv in
      let* src = T.Chk.run tac_src D.TpDim in
      let* trg = T.Chk.run tac_trg D.TpDim in
      let* fam_src = RM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, src)) in
      let+ tm = T.Chk.run tac_tm fam_src
      and+ fam_trg = RM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, trg)) in
      S.Coe (fam, src, trg, tm), fam_trg


  let hcom_bdy_tp tp r phi =
    RM.lift_cmp @@
    Sem.splice_tp @@
    Splice.con r @@ fun src ->
    Splice.con phi @@ fun cof ->
    Splice.tp tp @@ fun vtp ->
    Splice.term @@
    TB.pi TB.tp_dim @@ fun i ->
    TB.pi (TB.tp_prf (TB.join [TB.eq i src; cof])) @@ fun _ ->
    vtp

  let hcom (tac_code : T.Chk.tac) (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_cof : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Univ.hcom" @@
      let* code = T.Chk.run tac_code D.Univ in
      let* src = T.Chk.run tac_src D.TpDim in
      let* trg = T.Chk.run tac_trg D.TpDim in
      let* cof = T.Chk.run tac_cof D.TpCof in
      let* vsrc = RM.lift_ev @@ Sem.eval src in
      let* vcof = RM.lift_ev @@ Sem.eval cof in
      let* vtp = RM.lift_ev @@ Sem.eval_tp @@ S.El code in
      (* (i : dim) -> (_ : [i=src \/ cof]) -> A *)
      let+ tm = T.Chk.run tac_tm @<< hcom_bdy_tp vtp vsrc vcof in
      S.HCom (code, src, trg, cof, tm), vtp

  let hcom_chk (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Chk.tac =
    let as_code = function
      | D.ElStable code -> RM.ret @@ D.StableCode code
      | D.ElUnstable code -> RM.ret @@ D.UnstableCode code
      | D.ElCut cut -> RM.ret @@ D.Cut { tp = D.Univ; cut }
      | tp -> RM.expected_connective `El tp
    in
    let cool_hcom =
      T.Chk.brule ~name:"Univ.hcom_chk" @@ fun (tp, phi, tm_clo) ->
      let* tp = RM.lift_cmp @@ Sem.whnf_tp_ tp in
      match tp with
      | D.Sub (sub_tp, psi, _) ->
        Debug.print "Sub type: %a@." D.pp_tp sub_tp;
        let tac_code =
          T.Chk.brule @@ fun (_, _, _) ->
          let* vcode = as_code sub_tp in
          RM.quote_con D.Univ vcode
        in
        let tac_cof =
          T.Chk.brule @@ fun (_, _, _) ->
          RM.quote_cof @@ D.Cof.join [phi; psi]
        in
        let hcom_tac =
          Sub.intro @@
          T.Chk.syn @@
          hcom tac_code tac_src tac_trg tac_cof tac_tm in
        T.Chk.brun hcom_tac (tp, phi, tm_clo)
      | _ -> RM.expected_connective `Sub tp
    in
    Probe.try_with_boundary cool_hcom @@ fun tm ->
    T.Chk.brule @@ fun (tp, phi, tm_clo) ->
    let* () = RM.print_boundary tm tp phi tm_clo in
    T.Chk.brun (Hole.silent_hole None) (tp, phi, tm_clo)

  let com (tac_fam : T.Chk.tac) (tac_src : T.Chk.tac) (tac_trg : T.Chk.tac) (tac_cof : T.Chk.tac) (tac_tm : T.Chk.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Univ.com" @@
      let* piuniv =
        RM.lift_cmp @@
        Sem.splice_tp @@
        Splice.term @@
        TB.pi TB.tp_dim @@ fun _i ->
        TB.univ
      in
      let* fam = T.Chk.run tac_fam piuniv in
      let* src = T.Chk.run tac_src D.TpDim in
      let* trg = T.Chk.run tac_trg D.TpDim in
      let* cof = T.Chk.run tac_cof D.TpCof in
      let* vfam = RM.lift_ev @@ Sem.eval fam in
      let* vsrc = RM.lift_ev @@ Sem.eval src in
      let* vcof = RM.lift_ev @@ Sem.eval cof in
      (* (i : dim) -> (_ : [i=src \/ cof]) -> A i *)
      let+ tm =
        T.Chk.run tac_tm @<<
        RM.lift_cmp @@
        Sem.splice_tp @@
        Splice.con vfam @@ fun vfam ->
        Splice.con vsrc @@ fun src ->
        Splice.con vcof @@ fun cof ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.pi (TB.tp_prf (TB.join [TB.eq i src; cof])) @@ fun _ ->
        TB.el @@ TB.ap vfam [i]
      and+ vfam_trg = RM.lift_ev @@ Sem.eval_tp @@ S.El (S.Ap (fam, trg)) in
      S.Com (fam, src, trg, cof, tm), vfam_trg
end


module Signature =
struct
  let formation (tacs : T.Tp.tac telescope) : T.Tp.tac =
    let rec form_tele =
      function
      | Bind (lbl, tac, tacs) ->
        let* tp = T.Tp.run tac in
        let* vtp = RM.lift_ev @@ Sem.eval_tp tp in
        T.abstract ~ident:(lbl :> Ident.t) vtp @@ fun var ->
        let+ tele = form_tele (tacs var) in
        S.Cell ((lbl :> Ident.t), tp, tele)
      | Done ->
        RM.ret @@ S.Empty
    in
    T.Tp.rule ~name:"Signature.formation" @@
      let+ tele = form_tele tacs
      in S.Signature tele

  (* Check that [tele0] is a prefix of [tele1], and return the rest of [tele1]
     along with the quoted eta-expansion of [con], which has type [sign0]
  *)
  let equate_tele_prefix tele0 tele1 con ~renaming =
    let rec go n projs tele0 tele1 =
      match tele0, tele1 with
      | D.Empty, _ ->
        RM.ret (Bwd.to_list projs, tele1)

      (* Matching fields *)
      | D.Cell (lbl0, tp0, clo0), D.Cell (lbl1, tp1, clo1) when Ident.equal (Option.value ~default:lbl0 (renaming lbl0)) lbl1 ->
        let* () = RM.equate_tp tp0 tp1 in
        let* proj = RM.lift_cmp @@ Sem.do_proj con lbl0 n in
        let* qproj = RM.quote_con tp0 proj in
        let* tele0 = RM.lift_cmp @@ Sem.inst_tele_clo clo0 proj in
        let* tele1 = RM.lift_cmp @@ Sem.inst_tele_clo clo1 proj in
        go (n + 1) (projs #< (lbl0, qproj)) tele0 tele1

      (* Extra field in included sign *)
      | D.Cell (lbl0, _, clo0), _ ->
        let* proj = RM.lift_cmp @@ Sem.do_proj con lbl0 n in
        let* tele0 = RM.lift_cmp @@ Sem.inst_tele_clo clo0 proj in
        go (n + 1) projs tele0 tele1
    in go 0 Emp tele0 tele1

  let intro_fields phi phi_clo (tele : D.tele) (tacs : [`Field of Ident.t * T.Chk.tac | `Include of T.Syn.tac * (Ident.t -> Ident.t option)] list) : S.fields m =
    let rec go fields n tele tacs =
      match tele, tacs with
      (* The sig and struct labels line up, run the tactic and add the field *)
      | D.Cell (lbl0, tp, clo), `Field (lbl1, tac) :: tacs when Ident.equal lbl0 lbl1 ->
        let* tfield = T.Chk.brun tac (tp, phi, D.un_lam @@ D.compose (D.proj lbl0 n) @@ D.Lam (Ident.anon, phi_clo)) in
        let* vfield = RM.lift_ev @@ Sem.eval tfield in
        let* tele = RM.lift_cmp @@ Sem.inst_tele_clo clo vfield in
        go (fields #< (lbl0, tfield)) (n + 1) tele tacs

      (* The labels do not line up.
         If the sig field is a nullary extension type then we fill it automatically
         and continue with our list of struct tactics unchanged.
         Otherwise we ignore the extra field
      *)
      | D.Cell (lbl, tp, clo), (`Field _ :: tacs as all_tacs) ->
        Univ.is_nullary_ext tp |>> begin function
          | true ->
            let* tfield = T.Chk.brun Univ.infer_nullary_ext (tp, phi, D.un_lam @@ D.compose (D.proj lbl n) @@ D.Lam (Ident.anon, phi_clo)) in
            let* vfield = RM.lift_ev @@ Sem.eval tfield in
            let* tele = RM.lift_cmp @@ Sem.inst_tele_clo clo vfield in
            go (fields #< (lbl, tfield)) (n + 1) tele all_tacs
          | false ->
            go fields n tele tacs
        end

      (* There are no more struct tactics.
         If the sig field is a nullary extension type then we fill it automatically.
         Otherwise the field is missing, so we unleash a hole for it
      *)
      | D.Cell (lbl,tp, clo), [] ->
        let* tac = Univ.is_nullary_ext tp |>> function
          | true -> RM.ret Univ.infer_nullary_ext
          | false -> RM.ret @@ Hole.unleash_hole @@ Ident.to_string_opt lbl
        in
        let* tfield = T.Chk.brun tac (tp, phi, D.un_lam @@ D.compose (D.proj lbl n) @@ D.Lam (Ident.anon, phi_clo)) in
        let* vfield = RM.lift_ev @@ Sem.eval tfield in
        let* tele = RM.lift_cmp @@ Sem.inst_tele_clo clo vfield in
        go (fields #< (lbl, tfield)) (n + 1) tele []

      (* Including the fields of another struct *)
      | tele, `Include (tac,renaming) :: tacs ->
        let* tm,tp = T.Syn.run tac in
        RM.lift_cmp @@ Sem.whnf_tp_ tp |>> begin function
          | D.Signature inc_sign ->
            let* vtm = RM.lift_ev @@ Sem.eval tm in
            let* inc_fields, tele = equate_tele_prefix ~renaming inc_sign tele vtm in
            go (Bwd.append fields inc_fields) (n + List.length inc_fields) tele tacs
          | _ ->
            RM.with_pp @@ fun ppenv ->
            RM.refine_err @@ Err.ExpectedStructure (ppenv, tm)
        end

      (* There are no extra fields, we're done *)
      | D.Empty, `Field _ :: _
      | D.Empty,[] ->
        RM.ret @@ Bwd.to_list fields
    in
    let+ fields = go Emp 0 tele tacs in
    S.Fields fields

  let intro (tacs : [`Field of Ident.t * T.Chk.tac | `Include of T.Syn.tac * (Ident.t -> Ident.t option)] list) : T.Chk.tac =
    T.Chk.brule ~name:"Signature.intro" @@
    function
    | (D.Signature sign, phi, phi_clo) ->
      let+ fields = intro_fields phi phi_clo sign tacs in
      S.Struct fields
    | (tp, _, _) -> RM.expected_connective `Signature tp

  let proj_tp (tele : D.tele) (tstruct : S.t) (lbl : Ident.t) : (D.tp * int) m =
    let rec go n =
      function
      | D.Cell (flbl, tp, _) when Ident.equal flbl lbl -> RM.ret (tp, n)
      | D.Cell (flbl, __, clo) ->
        let* vfield = RM.lift_ev @@ Sem.eval @@ S.Proj (tstruct, flbl, n) in
        let* tele = RM.lift_cmp @@ Sem.inst_tele_clo clo vfield in
        go (n + 1) tele
      | D.Empty -> RM.expected_field tele tstruct lbl
    in go 0 tele

  let proj tac lbl : T.Syn.tac =
    T.Syn.rule ~name:"Signature.proj" @@
      let* tstruct, tp = T.Syn.run tac in
      match tp with
      | D.Signature sign ->
        let+ (tp, n) = proj_tp sign tstruct lbl in
        S.Proj (tstruct, lbl, n), tp
      | _ -> RM.expected_connective `Signature tp
end


module El =
struct
  let formation tac =
    T.Tp.rule ~name:"El.formation" @@
      let+ tm = T.Chk.run tac D.Univ in
      S.El tm

  let dest_el tp =
    match tp with
    | D.ElStable con ->
      RM.lift_cmp @@ Sem.unfold_el con
    | _ ->
      RM.expected_connective `El tp

  let intro tac =
    T.Chk.brule ~name:"El.intro" @@ fun (tp, phi, clo) ->
    let* unfolded = dest_el tp in
    let+ tm = T.Chk.brun tac (unfolded, phi, D.un_lam @@ D.compose D.el_out @@ D.Lam (Ident.anon, clo)) in
    S.ElIn tm

  let elim tac =
    T.Syn.rule ~name:"El.elim" @@
      let* tm, tp = T.Syn.run tac in
      let+ unfolded = dest_el tp in
      S.ElOut tm, unfolded
end


module ElV =
struct
  let intro (tac_part : T.Chk.tac) (tac_tot : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"ElV.intro" @@
    function
    | D.ElUnstable (`V (r, pcode, code, pequiv)), phi, clo ->
      let* part =
        let* tp_part =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.con pcode @@ fun pcode ->
          Splice.dim r @@ fun r ->
          Splice.term @@
          TB.pi (TB.tp_prf (TB.eq r TB.dim0)) @@ fun _ ->
          TB.el @@ TB.ap pcode [TB.prf]
        in
        let* bdry_fn =
          RM.lift_cmp @@ Sem.splice_tm @@
          Splice.clo clo @@ fun clo ->
          Splice.term @@
          TB.lam @@ fun _ ->
          TB.lam @@ fun _ ->
          TB.ap clo [TB.prf]
        in
        T.Chk.brun tac_part (tp_part, phi, D.un_lam bdry_fn)
      in
      let* tot =
        let* tp = RM.lift_cmp @@ Sem.do_el code in
        let* vpart = RM.lift_ev @@ Sem.eval part in
        let* bdry_fn =
          RM.lift_cmp @@ Sem.splice_tm @@
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
        T.Chk.brun tac_tot (tp, CofBuilder.join [CofBuilder.eq0 r; phi], D.un_lam bdry_fn)
      in
      let* tr = RM.quote_dim r in
      let+ t_pequiv =
        let* tp_pequiv =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
        in
        RM.quote_con tp_pequiv pequiv
      in
      S.VIn (tr, t_pequiv, part, tot)
    | tp, _, _ ->
      RM.expected_connective `ElV tp

  let elim (tac_v : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule ~name:"ElV.elim" @@
      let* tm, tp = T.Syn.run tac_v in
      match tp with
      | D.ElUnstable (`V (r, pcode, code, pequiv)) ->
        let* tr = RM.quote_dim r in
        let* tpcode = RM.quote_con (D.Pi (D.TpPrf (CofBuilder.eq0 r), Ident.anon, D.const_tp_clo D.Univ)) pcode in
        let* tcode = RM.quote_con D.Univ code in
        let* t_pequiv =
          let* tp_pequiv =
            RM.lift_cmp @@ Sem.splice_tp @@
            Splice.Macro.tp_pequiv_in_v ~r ~pcode ~code
          in
          RM.quote_con tp_pequiv pequiv
        in
        let vproj = S.VProj (tr, tpcode, tcode, t_pequiv, tm) in
        let* tp_vproj = RM.lift_cmp @@ Sem.do_el code in
        RM.ret (vproj, tp_vproj)
      | _ ->
        RM.expected_connective `ElV tp
end

module ElHCom =
struct
  let intro (tac_walls : T.Chk.tac) (tac_cap : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"ElHCom.intro" @@
    function
    | D.ElUnstable (`HCom (r, r', phi, bdy)), psi, psi_clo ->
      let* twalls =
        let* tp_walls =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.cof phi @@ fun phi ->
          Splice.con bdy @@ fun bdy ->
          Splice.dim r' @@ fun r' ->
          Splice.term @@ TB.pi (TB.tp_prf phi) @@ fun _ -> TB.el @@ TB.ap bdy [r'; TB.prf]
        in
        let* bdry_fn =
          RM.lift_cmp @@ Sem.splice_tm @@
          Splice.clo psi_clo @@ fun psi_clo ->
          Splice.term @@
          TB.lam @@ fun _ -> (* [psi] *)
          TB.lam @@ fun _ -> (* [phi] *)
          TB.ap psi_clo [TB.prf]
        in
        T.Chk.brun tac_walls (tp_walls, psi, D.un_lam bdry_fn)
      in
      let+ tcap =
        let* walls = RM.lift_ev @@ Sem.eval twalls in
        let* tp_cap =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.con bdy @@ fun bdy ->
          Splice.dim r @@ fun r ->
          Splice.term @@ TB.el @@ TB.ap bdy [r; TB.prf]
        in
        let* bdry_fn =
          RM.lift_cmp @@ Sem.splice_tm @@
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
             phi, TB.coe (TB.lam ~ident:(Ident.machine "i") @@ fun i -> TB.ap bdy [i; TB.prf]) r' r (TB.ap walls [TB.prf])]
        in
        T.Chk.brun tac_cap (tp_cap, CofBuilder.join [phi; psi], D.un_lam bdry_fn)
      and+ tr = RM.quote_dim r
      and+ tr' = RM.quote_dim r'
      and+ tphi = RM.quote_cof phi in
      S.Box (tr, tr', tphi, twalls, tcap)

    | tp, _, _ ->
      RM.expected_connective `ElHCom tp

  let elim (tac_box : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule ~name:"ElHCom.elim" @@
      let* box, box_tp = T.Syn.run tac_box in
      match box_tp with
      | D.ElUnstable (`HCom (r, r', phi, bdy)) ->
        let+ tr = RM.quote_dim r
        and+ tr' = RM.quote_dim r'
        and+ tphi = RM.quote_cof phi
        and+ tbdy =
          let* tp_bdy = Univ.hcom_bdy_tp D.Univ (D.dim_to_con r) (D.cof_to_con phi) in
          RM.quote_con tp_bdy bdy
        and+ tp_cap =
          let* code_fib = RM.lift_cmp @@ Sem.do_ap2 bdy (D.dim_to_con r) D.Prf in
          RM.lift_cmp @@ Sem.do_el code_fib
        in
        S.Cap (tr, tr', tphi, tbdy, box), tp_cap
      | _ ->
        RM.expected_connective `ElHCom box_tp
end


module Structural =
struct

  let lookup_var id : T.Syn.tac =
    T.Syn.rule ~name:"Structural.lookup_var" @@
      let* res = RM.resolve id in
      match res with
      | `Local ix ->
        let+ tp = RM.get_local_tp ix in
        S.Var ix, tp
      | `Global sym ->
        let+ tp = RM.get_global sym in
        S.Global sym, tp
      | `Unbound ->
        RM.refine_err @@ Err.UnboundVariable id

  let index ix =
    let+ tp = RM.get_local_tp ix in
    S.Var ix, tp

  let level lvl =
    T.Syn.rule ~name:"Structural.level" @@
      let* env = RM.read in
      let ix = RefineEnv.size env - lvl - 1 in
      index ix


  let rec intros ~cells tac =
    match cells with
    | [] ->
      tac
    | cell :: cells ->
      let ident = Env.Cell.ident cell in
      Pi.intro ~ident @@ fun _ ->
      intros ~cells tac

  let unleash_toplevel ~name ?unf_sym ~unf_cof (tac : T.Chk.tac) =
    fun (tp, phi, clo) ->
    let* env = RM.read in
    let cells = Env.locals env in
    let cells_fwd = BwdLabels.to_list cells in
    let* cut =
      RM.globally @@
      let* vtp =
        let* tp = RM.multi_pi cells_fwd @@ RM.quote_tp (D.Sub (tp, phi, clo)) in
        RM.lift_ev @@ Sem.eval_tp tp
      in
      let* tp_of_goal =
        RM.lift_cmp @@ Sem.splice_tp @@
        Splice.tp vtp @@ fun vtp ->
        Splice.cof unf_cof @@ fun cof ->
        Splice.term @@ TB.pi (TB.tp_prf cof) @@ fun _ -> vtp
      in
      let* vdef =
        let* tm = tp_of_goal |> T.Chk.run @@ Pi.intro @@ fun _ -> intros ~cells:cells_fwd tac in
        RM.lift_ev @@ Sem.eval tm
      in
      let* tp_sub =
        RM.lift_cmp @@ Sem.splice_tp @@
        Splice.tp vtp @@ fun vtp ->
        Splice.con vdef @@ fun vtm ->
        Splice.cof unf_cof @@ fun cof ->
        Splice.term @@ TB.sub vtp cof @@ fun prf -> TB.ap vtm [prf]
      in
      let* sym = RM.add_global ~unfolder:unf_sym ~shadowing:false name tp_sub in
      let hd = D.UnstableCut ((D.Global sym, []), D.KSubOut (unf_cof, D.const_tm_clo vdef)) in
      RM.ret @@ RM.multi_ap cells (hd, [])
    in
    let+ tm = RM.quote_cut cut in
    S.SubOut tm

  let abstract ~name (tac : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"Structural.abstract" @@ fun goal ->
    let name = Option.value name ~default:Ident.anon in
    let* unf_sym = RM.add_global ~unfolder:None ~shadowing:false (Ident.unfolder name) D.TpDim in
    let* unf_dim = RM.eval @@ S.Global unf_sym in
    let* unf_cof = RM.lift_cmp @@ Sem.con_to_cof @@ D.CofBuilder.eq1 unf_dim in
    unleash_toplevel ~name ~unf_sym ~unf_cof tac goal

  let unfold (unfoldings : Ident.t list) (tac : T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"Structural.unfold" @@ fun goal ->
    let* unf_cof =
      let* syms = RM.resolve_unfolder_syms unfoldings in
      let* dims = syms |> RMU.map @@ fun sym -> RM.eval @@ S.Global sym in
      RM.lift_cmp @@
      Sem.con_to_cof @@
      D.CofBuilder.meet @@
      List.map D.CofBuilder.eq1 dims
    in
    unleash_toplevel ~name:(Ident.blocked unfoldings) ~unf_cof tac goal

  let generalize ident (tac : T.Chk.tac) : T.Chk.tac =
    T.Chk.rule ~name:"Structural.generalize" @@
      fun tp ->
      let* env = RM.read in
      let* lvl =
        RM.resolve ident |>>
        function
        | `Local ix -> RM.ret @@ RefineEnv.size env - ix - 1
        | _ -> RM.refine_err @@ Err.UnboundVariable ident
      in

      let cells = Env.locals env in
      let cells_fwd = BwdLabels.to_list cells in

      let* cut =
        RM.globally @@
        let* global_tp =
          let* tp = RM.multi_pi cells_fwd @@ RM.quote_tp tp in
          RM.lift_ev @@ Sem.eval_tp tp
        in
        let* vdef =
          let prefix = List.take lvl cells_fwd in
          let* tm = global_tp |> T.Chk.run @@ intros ~cells:prefix tac in
          RM.lift_ev @@ Sem.eval tm
        in
        let* tp_sub =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.tp global_tp @@ fun vtp ->
          Splice.con vdef @@ fun vtm ->
          Splice.term @@
          TB.sub vtp TB.top @@ fun _ -> vtm
        in
        let* sym = RM.add_global ~unfolder:None ~shadowing:true Ident.anon tp_sub in
        let top = Kado.Syntax.Free.top in
        let hd = D.UnstableCut ((D.Global sym, []), D.KSubOut (top, D.const_tm_clo vdef)) in
        RM.ret @@ RM.multi_ap cells (hd, [])
      in
      RM.quote_cut cut

  let let_ ?(ident = Ident.anon) (tac_def : T.Syn.tac) (tac_bdy : T.var -> T.Chk.tac) : T.Chk.tac =
    T.Chk.brule ~name:"Structural.let_" @@ fun goal ->
    let* tdef, tp_def = T.Syn.run tac_def in
    let* vdef = RM.lift_ev @@ Sem.eval tdef in
    let* tbdy =
      let* const_vdef =
        RM.lift_cmp @@ Sem.splice_tm @@ Splice.con vdef @@ fun vdef ->
        Splice.term @@ TB.lam @@ fun _ -> vdef
      in
      T.abstract ~ident (D.Sub (tp_def, CofBuilder.top, D.un_lam const_vdef)) @@ fun var ->
      T.Chk.brun (tac_bdy var) goal
    in
    RM.ret @@ S.Let (S.SubIn tdef, ident, tbdy)

  let let_syn ?(ident = Ident.anon) (tac_def : T.Syn.tac) (tac_bdy : T.var -> T.Syn.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Structural.let_syn" @@
      let* tdef, tp_def = T.Syn.run tac_def in
      let* vdef = RM.lift_ev @@ Sem.eval tdef in
      let* tbdy, tbdytp =
        let* const_vdef =
          RM.lift_cmp @@ Sem.splice_tm @@ Splice.con vdef @@ fun vdef ->
          Splice.term @@ TB.lam @@ fun _ -> vdef
        in
        T.abstract ~ident (D.Sub (tp_def, CofBuilder.top, D.un_lam const_vdef)) @@ fun var ->
        let* tbdy, bdytp = T.Syn.run @@ tac_bdy var in
        let* tbdytp = RM.quote_tp bdytp in
        RM.ret (tbdy, tbdytp)
      in
      let* bdytp = RM.lift_ev @@ EvM.append [D.SubIn vdef] @@ Sem.eval_tp tbdytp in
      RM.ret (S.Let (S.SubIn tdef, ident, tbdy), bdytp)

end


module Nat =
struct
  let formation =
    T.Tp.rule ~name:"Nat.formation" @@
      RM.ret S.Nat

  let assert_nat =
    function
    | D.Nat -> RM.ret ()
    | tp -> RM.expected_connective `Nat tp

  let rec int_to_term =
    function
    | 0 -> S.Zero
    | n -> S.Suc (int_to_term (n - 1))

  let literal n : T.Chk.tac =
    T.Chk.rule ~name:"Nat.literal" @@
      fun tp ->
      let+ () = assert_nat tp in
      int_to_term n

  let suc tac : T.Chk.tac =
    T.Chk.rule ~name:"Nat.suc" @@
      fun tp ->
      let* () = assert_nat tp in
      let+ t = T.Chk.run tac tp in
      S.Suc t

  let elim (tac_mot : T.Chk.tac) (tac_case_zero : T.Chk.tac) (tac_case_suc : T.Chk.tac) (tac_scrut : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Nat.elim" @@
      let* tscrut, nattp = T.Syn.run tac_scrut in
      let* () = assert_nat nattp in
      let* tmot =
        T.Chk.run tac_mot @<<
        RM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@
        TB.pi TB.nat @@ fun _ -> TB.univ
      in
      let* vmot = RM.lift_ev @@ Sem.eval tmot in

      let* tcase_zero =
        let* code = RM.lift_cmp @@ Sem.do_ap vmot D.Zero in
        let* tp = RM.lift_cmp @@ Sem.do_el code in
        T.Chk.run tac_case_zero tp
      in

      let* tcase_suc =
        let* suc_tp =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.con vmot @@ fun mot ->
          Splice.term @@
          TB.pi TB.nat @@ fun x ->
          TB.pi (TB.el (TB.ap mot [x])) @@ fun _ih ->
          TB.el @@ TB.ap mot [TB.suc x]
        in
        T.Chk.run tac_case_suc suc_tp
      in

      let+ fib_scrut =
        let* vscrut = RM.lift_ev @@ Sem.eval tscrut in
        let* code = RM.lift_cmp @@ Sem.do_ap vmot vscrut in
        RM.lift_cmp @@ Sem.do_el code
      in

      S.NatElim (tmot, tcase_zero, tcase_suc, tscrut), fib_scrut
end


module Circle =
struct
  let formation =
    T.Tp.rule ~name:"Circle.formation" @@
      RM.ret S.Circle

  let assert_circle =
    function
    | D.Circle -> RM.ret ()
    | tp -> RM.expected_connective `Circle tp

  let base =
    T.Chk.rule ~name:"Circle.base" @@ fun tp ->
      let+ () = assert_circle tp in
      S.Base

  let loop tac : T.Chk.tac =
    T.Chk.rule ~name:"Circle.loop" @@ fun tp ->
      let* () = assert_circle tp in
      let+ r = T.Chk.run tac D.TpDim in
      S.Loop r

  let elim (tac_mot : T.Chk.tac) (tac_case_base : T.Chk.tac) (tac_case_loop : T.Chk.tac) (tac_scrut : T.Syn.tac) : T.Syn.tac =
    T.Syn.rule ~name:"Circle.elim" @@
      let* tscrut, circletp = T.Syn.run tac_scrut in
      let* () = assert_circle circletp in
      let* tmot =
        T.Chk.run tac_mot @<<
        RM.lift_cmp @@ Sem.splice_tp @@ Splice.term @@
        TB.pi TB.circle @@ fun _ -> TB.univ
      in
      let* vmot = RM.lift_ev @@ Sem.eval tmot in

      let* tcase_base =
        let* code = RM.lift_cmp @@ Sem.do_ap vmot D.Base in
        let* tp = RM.lift_cmp @@ Sem.do_el code in
        T.Chk.run tac_case_base tp
      in

      let* tcase_loop =
        let* loop_tp =
          RM.lift_cmp @@ Sem.splice_tp @@
          Splice.con vmot @@ fun mot ->
          Splice.term @@
          TB.pi TB.tp_dim @@ fun x ->
          TB.el @@ TB.ap mot [TB.loop x]
        in
        T.Chk.run tac_case_loop loop_tp
      in

      let+ fib_scrut =
        let* vscrut = RM.lift_ev @@ Sem.eval tscrut in
        let* code = RM.lift_cmp @@ Sem.do_ap vmot vscrut in
        RM.lift_cmp @@ Sem.do_el code
      in

      S.CircleElim (tmot, tcase_base, tcase_loop, tscrut), fib_scrut
end
