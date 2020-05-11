module S = Syntax
module D = Domain


exception Todo

open CoolBasis
open Bwd

exception NbeFailed of string

module Splice = Splice
module TB = TermBuilder

module CM = struct include Monads.CmpM include Monad.Notation (Monads.CmpM) module MU = Monad.Util (Monads.CmpM) end
module EvM = struct include Monads.EvM include Monad.Notation (Monads.EvM) module MU = Monad.Util (Monads.EvM) end

type 'a whnf = [`Done | `Reduce of 'a]


let get_local i =
  let open EvM in
  let* env = EvM.read_local in
  match Bwd.nth env.conenv i with
  | v -> EvM.ret v
  | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"

let get_local_tp i =
  let open EvM in
  let* env = EvM.read_local in
  match Bwd.nth env.tpenv i with
  | v -> EvM.ret v
  | exception _ -> EvM.throw @@ NbeFailed "Variable out of bounds"


let tri_test_cof phi =
  let open CM in
  test_sequent [] phi |>>
  function
  | true -> CM.ret `True
  | false ->
    test_sequent [phi] Cof.bot |>>
    function
    | true -> ret `False
    | false -> ret `Indet

let rec normalize_cof phi =
  let open CM in
  match phi with
  | Cof.Cof (Cof.Eq _) | Cof.Var _ ->
    begin
      tri_test_cof phi |>>
      function
      | `True -> ret Cof.top
      | `False -> ret Cof.bot
      | `Indet -> ret phi
    end
  | Cof.Cof (Cof.Join phis) ->
    let+ phis = MU.map normalize_cof phis in
    Cof.join phis
  | Cof.Cof (Cof.Meet phis) ->
    let+ phis = MU.map normalize_cof phis in
    Cof.meet phis


let con_to_dim =
  let open CM in
  function
  | D.DimCon0 -> ret D.Dim0
  | D.DimCon1 -> ret D.Dim1
  | D.Abort -> ret D.Dim0
  | D.Cut {cut = Var l, []} -> ret @@ D.DimVar l
  | D.Cut {cut = Global sym, []} -> ret @@ D.DimProbe sym
  | con ->
    Format.eprintf "bad: %a@." D.pp_con con;
    throw @@ NbeFailed "con_to_dim"


let rec cof_con_to_cof : (D.con, D.con) Cof.cof_f -> D.cof CM.m =
  let open CM in
  function
  | Cof.Eq (r, s) ->
    let+ r = con_to_dim r
    and+ s = con_to_dim s in
    Cof.eq r s
  | Cof.Join phis ->
    let+ phis = MU.map con_to_cof phis in
    Cof.join phis
  | Cof.Meet phis ->
    let+ phis = MU.map con_to_cof phis in
    Cof.meet phis

and con_to_cof =
  let open CM in
  function
  | Cof cof -> cof_con_to_cof cof
  | D.Cut {cut = D.Var l, []} -> ret @@ Cof.var l
  | _ -> throw @@ NbeFailed "con_to_cof"


let dest_pi_code con =
  let open CM in
  match con with
  | D.CodePi (base, fam) ->
    ret (base, fam)
  | _ ->
    throw @@ NbeFailed "Expected pi code"

let dest_sg_code con =
  let open CM in
  match con with
  | D.CodeSg (base, fam) ->
    ret (base, fam)
  | _ ->
    throw @@ NbeFailed "Expected pi code"


let rec eval_tp : S.tp -> D.tp EvM.m =
  let open EvM in
  function
  | S.Nat -> ret D.Nat
  | S.Pi (base, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Pi (vbase, D.TpClo (fam, env))
  | S.Sg (base, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Sg (vbase, D.TpClo (fam, env))
  | S.Univ ->
    ret D.Univ
  | S.El tm ->
    let* con = eval tm in
    lift_cmp @@ unfold_el con
  | S.GoalTp (lbl, tp) ->
    let+ tp = eval_tp tp in
    D.GoalTp (lbl, tp)
  | S.Sub (tp, tphi, tm) ->
    let+ env = read_local
    and+ tp = eval_tp tp
    and+ phi = eval_cof tphi in
    D.Sub (tp, phi, D.Clo (tm, env))
  | S.TpDim  ->
    ret D.TpDim
  | S.TpCof ->
    ret D.TpCof
  | S.TpPrf tphi ->
    let+ phi = eval_cof tphi in
    D.TpPrf phi
  | S.TpVar ix ->
    get_local_tp ix

and eval =
  let open EvM in
  function
  | S.Var i ->
    let* con = get_local i in
    begin
      lift_cmp @@ whnf_con con |>> function
      | `Done -> ret con
      | `Reduce con -> ret con
    end
  | S.Global sym ->
    let* st = EvM.read_global in
    let* veil = EvM.read_veil in
    let tp, ocon = ElabState.get_global sym st in
    begin
      match ocon, Veil.policy sym veil with
      | Some con, `Transparent -> ret con
      | _ ->
        ret @@ D.Cut {tp; cut = (D.Global sym, [])}
    end
  | S.Let (def, body) ->
    let* vdef = eval def in
    append [vdef] @@ eval body
  | S.Ann (term, _) ->
    eval term
  | S.Zero ->
    ret D.Zero
  | S.Suc t ->
    let+ con = eval t in
    D.Suc con
  | S.NatElim (mot, zero, suc, n) ->
    let* vzero = eval zero in
    let* vn = eval n in
    let* env = read_local in
    let clmot = D.TpClo (mot, env) in
    let clsuc = D.Clo (suc, env) in
    lift_cmp @@ do_nat_elim clmot vzero clsuc vn
  | S.Lam t ->
    let+ env = read_local in
    D.Lam (D.Clo (t, env))
  | S.Ap (t0, t1) ->
    let* con0 = eval t0 in
    let* con1 = eval t1 in
    lift_cmp @@ do_ap con0 con1
  | S.Pair (t1, t2) ->
    let+ el1 = eval t1
    and+ el2 = eval t2 in
    D.Pair (el1, el2)
  | S.Fst t ->
    let* con = eval t in
    lift_cmp @@ do_fst con
  | S.Snd t ->
    let* con = eval t in
    lift_cmp @@ do_snd con
  | S.GoalRet tm ->
    let+ con = eval tm in
    D.GoalRet con
  | S.GoalProj tm ->
    let* con = eval tm in
    lift_cmp @@ do_goal_proj con
  | S.Coe (tpcode, tr, ts, tm) ->
    let* r = eval_dim tr in
    let* s = eval_dim ts in
    let* con = eval tm in
    begin
      CM.test_sequent [] (Cof.eq r s) |> lift_cmp |>> function
      | true ->
        ret con
      | false ->
        let* coe_abs = eval tpcode in
        lift_cmp @@ do_rigid_coe coe_abs r s con
    end
  | S.HCom (tpcode, tr, ts, tphi, tm) ->
    let* r = eval_dim tr in
    let* s = eval_dim ts in
    let* phi = eval_cof tphi in
    let* vtpcode = eval tpcode in
    let* vbdy = eval tm in
    begin
      CM.test_sequent [] (Cof.join [Cof.eq r s; phi]) |> lift_cmp |>> function
      | true ->
        lift_cmp @@ do_ap2 vbdy (D.dim_to_con s) D.Prf
      | false ->
        lift_cmp @@ do_rigid_hcom vtpcode r s phi vbdy
    end
  | S.Com (tpcode, tr, ts, tphi, tm) ->
    let* r = eval_dim tr in
    let* s = eval_dim ts in
    let* phi = eval_cof tphi in
    begin
      CM.test_sequent [] (Cof.join [Cof.eq r s; phi]) |> lift_cmp |>> function
      | true ->
        append [D.dim_to_con s] @@ eval tm
      | false ->
        let* bdy = eval tm in
        let* vtpcode = eval tpcode in
        lift_cmp @@ do_rigid_com vtpcode r s phi bdy
    end
  | S.SubOut tm ->
    let* con = eval tm in
    lift_cmp @@ do_sub_out con
  | S.SubIn t ->
    let+ con = eval t in
    D.SubIn con
  | S.Dim0 -> ret D.DimCon0
  | S.Dim1 -> ret D.DimCon1
  | S.Cof cof_f ->
    begin
      match cof_f with
      | Cof.Eq (tr, ts) ->
        let+ r = eval tr
        and+ s = eval ts in
        D.Cof (Cof.Eq (r, s))
      | Cof.Join tphis ->
        let+ phis = MU.map eval tphis in
        D.Cof (Cof.Join phis)
      | Cof.Meet tphis ->
        let+ phis = MU.map eval tphis in
        D.Cof (Cof.Meet phis)
    end
  | S.CofSplit (ttp, tphi0, tphi1, tm0, tm1) ->
    let* tp = eval_tp ttp in
    let* phi0 = eval_cof tphi0 in
    let* phi1 = eval_cof tphi1 in
    let* con =
      let+ env = read_local in
      let pclo0 = D.Clo (tm0, env) in
      let pclo1 = D.Clo (tm1, env) in
      let hd = D.Split (tp, phi0, phi1, pclo0, pclo1) in
      D.Cut {tp; cut = hd, []}
    in
    begin
      lift_cmp @@ whnf_con con |>> function
      | `Done -> ret con
      | `Reduce con -> ret con
    end
  | S.CofAbort ->
    ret D.Abort
  | S.Prf ->
    ret D.Prf

  | S.CodePath (fam, bdry) ->
    let* vfam = eval fam in
    let* vbdry = eval bdry in
    ret @@ D.CodePath (vfam, vbdry)

  | S.CodePi (base, fam) ->
    let+ vbase = eval base
    and+ vfam = eval fam in
    D.CodePi (vbase, vfam)

  | S.CodeSg (base, fam) ->
    let+ vbase = eval base
    and+ vfam = eval fam in
    D.CodeSg (vbase, vfam)

  | S.CodeNat ->
    ret D.CodeNat

and eval_dim tr =
  let open EvM in
  let* con = eval tr in
  lift_cmp @@ con_to_dim con

and eval_cof tphi =
  let open EvM in
  let* vphi = eval tphi in
  lift_cmp @@ con_to_cof vphi



and whnf_con : D.con -> D.con whnf CM.m =
  let open CM in
  function
  | D.Lam _ | D.Zero | D.Suc _ | D.Pair _ | D.GoalRet _ | D.Abort | D.SubIn _
  | D.Cof _ | D.DimCon0 | D.DimCon1 | D.Prf
  | D.CodePath _ | CodePi _ | D.CodeSg _ | D.CodeNat
  | D.Destruct _ ->
    ret `Done
  | D.Cut {cut} ->
    whnf_cut cut
  | D.FHCom (`Nat, r, s, phi, bdy) ->
    begin
      Cof.join [Cof.eq r s; phi] |> test_sequent [] |>> function
      | true ->
        reduce_to @<< do_ap2 bdy (D.dim_to_con s) D.Prf
      | false ->
        ret `Done
    end

and reduce_to con =
  let open CM in
  whnf_con con |>> function
  | `Done -> ret @@ `Reduce con
  | `Reduce con -> ret @@ `Reduce con

and plug_into sp con =
  let open CM in
  let* res = do_spine con sp in
  whnf_con res |>> function
  | `Done -> ret @@ `Reduce res
  | `Reduce res -> ret @@ `Reduce res

and whnf_hd hd =
  let open CM in
  match hd with
  | D.Global sym ->
    let* st = CM.read_global in
    begin
      match ElabState.get_global sym st with
      | tp, Some con ->
        reduce_to con
      | _, None | exception _ ->
        ret `Done
    end
  | D.Var _ -> ret `Done
  | D.Coe (abs, r, s, con) ->
    begin
      test_sequent [] (Cof.eq r s) |>> function
      | true -> reduce_to con
      | false ->
        begin
          let* dispatch = dispatch_rigid_coe abs r s con in
          match dispatch with
          | `Done ->
            ret `Done
          | `Reduce tag ->
            reduce_to @<< enact_rigid_coe abs r s con tag
        end
    end
  | D.HCom (cut, r, s, phi, bdy) ->
    begin
      Cof.join [Cof.eq r s; phi] |> test_sequent [] |>> function
      | true ->
        reduce_to @<< do_ap2 bdy (D.dim_to_con s) D.Prf
      | false ->
        whnf_cut cut |>> function
        | `Done ->
          ret `Done
        | `Reduce code ->
          begin
            let* dispatch = dispatch_rigid_hcom code r s phi bdy in
            match dispatch with
            | `Done _ ->
              ret `Done
            | `Reduce tag ->
              reduce_to @<< enact_rigid_hcom code r s phi bdy tag
          end
    end
  | D.SubOut (cut, phi, clo) ->
    begin
      test_sequent [] phi |>> function
      | true ->
        reduce_to @<< inst_tm_clo clo [D.Prf]
      | false ->
        whnf_cut cut |>> function
        | `Done ->
          ret `Done
        | `Reduce con ->
          reduce_to @<< do_sub_out con
    end
  | D.Split (tp, phi0, phi1, clo0, clo1) ->
    begin
      test_sequent [] phi0 |>> function
      | true ->
        reduce_to @<< inst_tm_clo clo0 [D.Prf]
      | false ->
        test_sequent [] phi1 |>> function
        | true ->
          reduce_to @<< inst_tm_clo clo1 [D.Prf]
        | false ->
          ret `Done
    end

and whnf_cut cut : D.con whnf CM.m =
  let open CM in
  let hd, sp = cut in
  whnf_hd hd |>>
  function
  | `Done -> ret `Done
  | `Reduce con -> plug_into sp con

and whnf_tp =
  let open CM in
  function
  | D.El cut ->
    begin
      whnf_cut cut |>> function
      | `Done -> ret `Done
      | `Reduce con ->
        let+ tp = unfold_el con  in
        `Reduce tp
    end
  | tp ->
    ret `Done

and do_nat_elim (mot : D.tp_clo) zero suc n : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match n with
  | D.Zero ->
    ret zero
  | D.Suc n ->
    let* v = do_nat_elim mot zero suc n in
    inst_tm_clo suc [n; v]
  | D.Cut {cut} ->
    let+ fib = inst_tp_clo mot [n] in
    cut_frm ~tp:fib ~cut @@
    D.KNatElim (mot, zero, suc)
  | D.FHCom (`Nat, r, s, phi, bdy) ->
    (* com (\i => mot (fhcom nat r i phi bdy)) r s phi (\i prf => nat_elim mot zero suc (bdy i prf)) *)
    splice_tm @@
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
      (*
      let fam = TB.lam @@ fun i -> inst_tp_clo mot [D.FHCom (`Nat, r, i, phi, bdy)] in
      let bdy' = TB.lam @@ fun i -> TB.lam @@ fun prf -> do_nat_elim mot zero suc (raise Todo) in
      *)
    TB.com (raise Todo) r s phi (raise Todo)
  | _ ->
    Format.eprintf "bad: %a@." D.pp_con n;
    CM.throw @@ NbeFailed "Not a number"

and cut_frm ~tp ~cut frm =
  D.Cut {tp; cut = D.push frm cut}

and inst_tp_clo : D.tp_clo -> D.con list -> D.tp CM.m =
  fun clo xs ->
  match clo with
  | TpClo (bdy, env) ->
    let open BwdNotation in
    CM.lift_ev {env with conenv = env.conenv <>< xs} @@
    eval_tp bdy

and inst_tm_clo : D.tm_clo -> D.con list -> D.con CM.m =
  fun clo xs ->
  match clo with
  | D.Clo (bdy, env) ->
    let open BwdNotation in
    CM.lift_ev {env with conenv = env.conenv <>< xs} @@
    eval bdy

and do_goal_proj con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match con with
  | D.GoalRet con -> ret con
  | D.Cut {tp = D.GoalTp (_, tp); cut} ->
    ret @@ cut_frm ~tp ~cut D.KGoalProj
  | _ ->
    CM.throw @@ NbeFailed "do_goal_proj"

and do_fst con : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match con with
  | D.Pair (con0, _) -> ret con0
  | D.Cut {tp = D.Sg (base, _); cut} ->
    ret @@ cut_frm ~tp:base ~cut D.KFst
  | _ ->
    throw @@ NbeFailed "Couldn't fst argument in do_fst"

and do_snd con : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match con with
  | D.Pair (_, con1) -> ret con1
  | D.Cut {tp = D.Sg (_, fam); cut} ->
    let* fst = do_fst con in
    let+ fib = inst_tp_clo fam [fst] in
    cut_frm ~tp:fib ~cut D.KSnd
  | _ ->
    throw @@ NbeFailed ("Couldn't snd argument in do_snd")


and do_ap2 f a b =
  let open CM in
  let* fa = do_ap f a in
  do_ap fa b

and do_ap f a =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match f with
  | D.Lam clo ->
    inst_tm_clo clo [a]

  | D.Destruct dst ->
    do_destruct dst a

  | D.Cut {tp = D.Pi (base, fam); cut} ->
    let+ fib = inst_tp_clo fam [a] in
    cut_frm ~tp:fib ~cut @@ D.KAp (base, a)

  | _ ->
    Format.eprintf "Bad: %a@." D.pp_con f;
    throw @@ NbeFailed "Not a function in do_ap"

and do_destruct dst a =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match dst, a with
  | D.DCodePiSplit, D.CodePi (base, fam)
  | D.DCodeSgSplit, D.CodeSg (base, fam) ->
    ret @@ D.Pair (base, fam)
  | D.DCodePathSplit, D.CodePath(fam, bdry) ->
    ret @@ D.Pair (fam, bdry)
  | _ ->
    throw @@ NbeFailed "Invalid destructor application"

and do_sub_out v =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match v with
  | D.SubIn con ->
    ret con
  | D.Cut {tp = D.Sub (tp, phi, clo); cut} ->
    ret @@ D.Cut {tp; cut = D.SubOut (cut, phi, clo), []}
  | _ ->
    throw @@ NbeFailed "do_sub_out"

and unfold_el : D.con -> D.tp CM.m =
  let open CM in
  fun con ->
  abort_if_inconsistent D.TpAbort @@
  match con with
  | D.Cut {cut} ->
    ret @@ D.El cut

  | D.CodeNat ->
    ret D.Nat

  | D.CodePi (base, fam) ->
    splice_tp @@
    Splice.foreign base @@ fun base ->
    Splice.foreign fam @@ fun fam ->
    Splice.term @@
    TB.pi (TB.el base) @@ fun x ->
    TB.el @@ TB.ap fam [x]

  | D.CodeSg (base, fam) ->
    splice_tp @@
    Splice.foreign base @@ fun base ->
    Splice.foreign fam @@ fun fam ->
    Splice.term @@
    TB.sg (TB.el base) @@ fun x ->
    TB.el @@ TB.ap fam [x]

  | D.CodePath (fam, bdry) ->
    splice_tp @@
    Splice.foreign fam @@ fun fam ->
    Splice.foreign bdry @@ fun bdry ->
    Splice.term @@
    TB.pi TB.tp_dim @@ fun i ->
    TB.sub (TB.el (TB.ap fam [i])) (TB.boundary i) @@ fun prf ->
    TB.ap bdry [i; prf]

  | con ->
    CM.throw @@ NbeFailed "unfold_el failed"

and do_coe r s (abs : D.con) con =
  let open CM in
  test_sequent [] (Cof.eq r s) |>> function
  | true -> ret con
  | _ -> do_rigid_coe abs r s con


and dispatch_rigid_coe line r s con =
  let open CM in
  let i = D.DimProbe (Symbol.named "do_rigid_coe") in
  let rec go peek =
    match peek with
    | D.CodePi _ ->
      ret @@ `Reduce `CoePi
    | D.CodeSg _ ->
      ret @@ `Reduce `CoeSg
    | D.CodePath _ ->
      ret @@ `Reduce `CoePath
    | D.CodeNat ->
      ret @@ `Reduce `CoeNat
    | D.Cut {cut} ->
      ret `Done
    | _ ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_coe"
  in
  go @<< do_ap line (D.dim_to_con i)

and dispatch_rigid_hcom code r s phi (bdy : D.con) =
  let open CM in
  let rec go code =
    match code with
    | D.CodePi (base, fam) ->
      ret @@ `Reduce (`HComPi (base, fam))
    | D.CodeSg (base, fam) ->
      ret @@ `Reduce (`HComSg (base, fam))
    | D.CodePath (fam, bdry) ->
      ret @@ `Reduce (`HComPath (fam, bdry))
    | D.CodeNat ->
      ret @@ `Reduce `HComNat
    | D.Cut {cut} ->
      ret @@ `Done cut
    | _ ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_hcom"
  in
  go code

and enact_rigid_coe line r s con tag =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match tag with
  | `CoeNat ->
    ret con
  | `CoePi ->
    let split_line = D.compose (D.Destruct D.DCodePiSplit) line in
    splice_tm @@
    Splice.foreign split_line @@ fun split_line ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign con @@ fun bdy ->
    let base_line = TB.lam @@ fun i -> TB.fst @@ TB.ap split_line [i] in
    let fam_line = TB.lam @@ fun i -> TB.snd @@ TB.ap split_line [i] in
    Splice.term @@ TB.Kan.coe_pi ~base_line ~fam_line ~r ~s ~bdy
  | `CoeSg ->
    let split_line = D.compose (D.Destruct D.DCodeSgSplit) line in
    splice_tm @@
    Splice.foreign split_line @@ fun split_line ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign con @@ fun bdy ->
    let base_line = TB.lam @@ fun i -> TB.fst @@ TB.ap split_line [i] in
    let fam_line = TB.lam @@ fun i -> TB.snd @@ TB.ap split_line [i] in
    Splice.term @@ TB.Kan.coe_sg ~base_line ~fam_line ~r ~s ~bdy
  | `CoePath ->
    let split_line = D.compose (D.Destruct D.DCodePathSplit) line in
    splice_tm @@
    Splice.foreign split_line @@ fun split_line ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign con @@ fun bdy ->
    let fam_line = TB.lam @@ fun i -> TB.fst @@ TB.ap split_line [i] in
    let bdry_line = TB.lam @@ fun i -> TB.snd @@ TB.ap split_line [i] in
    Splice.term @@ TB.Kan.coe_path ~fam_line ~bdry_line ~r ~s ~bdy

and enact_rigid_hcom code r s phi bdy tag =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match tag with
  | `HComPi (base, fam) ->
    splice_tm @@
    Splice.foreign base @@ fun base ->
    Splice.foreign fam @@ fun fam ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
    TB.Kan.hcom_pi ~base ~fam ~r ~s ~phi ~bdy
  | `HComSg (base, fam) ->
    splice_tm @@
    Splice.foreign base @@ fun base ->
    Splice.foreign fam @@ fun fam ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
    TB.Kan.hcom_sg ~base ~fam ~r ~s ~phi ~bdy
  | `HComPath (fam, bdry) ->
    splice_tm @@
    Splice.foreign fam @@ fun fam ->
    Splice.foreign bdry @@ fun bdry ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.term @@
    TB.Kan.hcom_path ~fam ~bdry ~r ~s ~phi ~bdy
  | `HComNat ->
    ret @@ D.FHCom (`Nat, r, s, phi, bdy)
  | `Done cut ->
    let tp = D.El cut in
    let hd = D.HCom (cut, r, s, phi, bdy) in
    ret @@ D.Cut {tp; cut = hd, []}

and do_rigid_coe (line : D.con) r s con =
  let open CM in
  CM.abort_if_inconsistent D.Abort @@
  let* tag = dispatch_rigid_coe line r s con in
  match tag with
  | `Done ->
    let hd = D.Coe (line, r, s, con) in
    let+ tp = unfold_el @<< do_ap line (D.dim_to_con s) in
    D.Cut {tp; cut = hd, []}
  | `Reduce tag ->
    enact_rigid_coe line r s con tag

and do_rigid_hcom code r s phi (bdy : D.con) =
  let open CM in
  CM.abort_if_inconsistent D.Abort @@
  let* tag = dispatch_rigid_hcom code r s phi bdy in
  match tag with
  | `Done cut ->
    let tp = D.El cut in
    let hd = D.HCom (cut, r, s, phi, bdy) in
    ret @@ D.Cut {tp; cut = hd, []}
  | `Reduce tag ->
    enact_rigid_hcom code r s phi bdy tag

and do_rigid_com (line : D.con) r s phi bdy =
  let open CM in
  let* code_s = do_ap line (D.dim_to_con s) in
  do_rigid_hcom code_s r s phi @<<
  splice_tm @@
  Splice.foreign_dim s @@ fun s ->
  Splice.foreign line @@ fun line ->
  Splice.foreign bdy @@ fun bdy ->
  Splice.term @@
  TB.lam @@ fun i ->
  TB.lam @@ fun prf ->
  TB.coe line i s @@
  TB.ap bdy [i; prf]

and force_lazy_con lcon : D.con CM.m =
  match lcon with
  | `Done con -> CM.ret con
  | `Do (con, spine) ->
    do_spine con spine

and do_frm con =
  function
  | D.KAp (_, con') -> do_ap con con'
  | D.KFst -> do_fst con
  | D.KSnd -> do_snd con
  | D.KNatElim (mot, case_zero, case_suc) -> do_nat_elim mot case_zero case_suc con
  | D.KGoalProj -> do_goal_proj con

and do_spine con =
  let open CM in
  function
  | [] -> ret con
  | k :: sp ->
    let* con' = do_frm con k in
    do_spine con' sp


and splice_tm t =
  let env, tm = Splice.compile t in
  CM.lift_ev env @@ eval tm

and splice_tp t =
  let env, tp = Splice.compile t in
  CM.lift_ev env @@ eval_tp tp


