module S = Syntax
module D = Domain


exception Todo
exception CJHM
exception CFHM
exception CCHM

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


module FaceLattice :
sig
  (** An atomic formula *)
  type atom = [`CofEq of D.dim * D.dim]

  (** A generator for a lattice homomorphism *)
  type gen = atom -> D.cof CM.m

  (** Extend a generator to a lattice homomorphism *)
  val extend : gen -> D.cof -> D.cof CM.m

  (** Quantifier elimination *)
  val forall : Symbol.t -> D.cof -> D.cof CM.m
end =
struct
  open CM

  type atom = [`CofEq of D.dim * D.dim]
  type gen = atom -> D.cof CM.m

  let extend gen =
    let rec loop =
      function
      | Cof.Var _ as phi -> ret phi
      | Cof.Cof phi ->
        match phi with
        | Cof.Join psis ->
          let+ psis = MU.map loop psis in
          Cof.Cof (Cof.Join psis)
        | Cof.Meet psis ->
          let+ psis = MU.map loop psis in
          Cof.Cof (Cof.Meet psis)
        | Cof.Eq (r, s) ->
          gen @@ `CofEq (r, s)
    in
    loop

  let forall sym =
    let i = D.DimProbe sym in
    extend @@
    function
    | `CofEq (r, s) ->
      test_sequent [] (Cof.eq r s) |>>
      function
      | true -> ret Cof.top
      | false ->
        test_sequent [] (Cof.eq i r) |>>
        function
        | true -> ret Cof.bot
        | false ->
          test_sequent [] (Cof.eq i s) |>>
          function
          | true -> ret Cof.bot
          | false -> ret @@ Cof.eq r s
end

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


let rec eval_tp : S.tp -> D.tp EvM.m =
  let open EvM in
  function
  | S.Nat -> ret D.Nat
  | S.Pi (base, ident, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Pi (vbase, ident, D.TpClo (fam, env))
  | S.Sg (base, ident, fam) ->
    let+ env = read_local
    and+ vbase = eval_tp base in
    D.Sg (vbase, ident, D.TpClo (fam, env))
  | S.Univ ->
    ret D.Univ
  | S.El tm ->
    let+ con = eval tm in
    D.El con
  | S.UnfoldEl tm ->
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
  | S.TpHCom (r, s, phi, bdy) ->
    raise Todo

and eval : S.t -> D.con EvM.m =
  let open EvM in
  fun tm ->
    match tm with
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
    | S.Let (def, _, body) ->
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
      let* vmot = eval mot in
      let* vzero = eval zero in
      let* vn = eval n in
      let* vsuc = eval suc in
      lift_cmp @@ do_nat_elim vmot vzero vsuc vn
    | S.Lam (ident, t) ->
      let+ env = read_local in
      D.Lam (ident, D.Clo (t, env))
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
    | S.SubIn tm ->
      let+ con = eval tm in
      D.SubIn con
    | S.ElOut tm ->
      let* con = eval tm in
      lift_cmp @@ do_el_out con
    | S.ElIn tm ->
      let+ con = eval tm in
      D.ElIn con
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
    | S.ForallCof tm ->
      let sym = Symbol.named "forall_probe" in
      let i = D.DimProbe sym in
      let* phi = append [D.dim_to_con i] @@ eval_cof tm in
      D.cof_to_con <@> lift_cmp @@ FaceLattice.forall sym phi
    | S.CofSplit (ttp, branches) ->
      let* tp = eval_tp ttp in
      let tphis, tms = List.split branches in
      let* phis = MU.map eval_cof tphis in
      let* con =
        let+ env = read_local in
        let pclos = List.map (fun tm -> D.Clo (tm, env)) tms in
        let hd = D.Split (tp, List.combine phis pclos) in
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

    | S.CodeUniv ->
      ret D.CodeUniv

    | S.Box (r, s, phi, sides, cap) ->
      let+ vr = eval_dim r
      and+ vs = eval_dim s
      and+ vphi = eval_cof phi
      and+ vsides = eval sides
      and+ vcap = eval cap in
      D.Box (vr, vs, vphi, vsides, vcap)

    | S.Cap (r, s, phi, code, box) ->
      let* vr = eval_dim r in
      let* vs = eval_dim s in
      let* vphi = eval_cof phi in
      let* vcode = eval code in
      let* vbox = eval box in
      begin
        lift_cmp @@ CM.test_sequent [] (Cof.join [Cof.eq vr vs; vphi]) |>>
        function
        | true ->
          lift_cmp @@
          splice_tm @@
          Splice.foreign_dim vr @@ fun r ->
          Splice.foreign_dim vs @@ fun s ->
          Splice.foreign_cof vphi @@ fun phi ->
          Splice.foreign vcode @@ fun code ->
          Splice.foreign vbox @@ fun box ->
          Splice.term @@
          TB.cof_split
            (TB.el @@ TB.ap code [s; TB.prf])
            [TB.eq r s, (fun _ -> box);
             phi, (fun _ -> TB.coe (TB.lam @@ fun i -> TB.ap code [i; TB.prf]) s r box)]
        | false ->
          raise CJHM
      end

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
  fun con ->
    match con with
    | D.Lam _ | D.Zero | D.Suc _ | D.Pair _ | D.GoalRet _ | D.Abort | D.SubIn _ | D.ElIn _
    | D.Cof _ | D.DimCon0 | D.DimCon1 | D.Prf
    | D.CodePath _ | CodePi _ | D.CodeSg _ | D.CodeNat | D.CodeUniv
    | D.Destruct _ ->
      ret `Done
    | D.Cut {cut} ->
      whnf_cut cut
    | D.FHCom (_, r, s, phi, bdy) ->
      begin
        test_sequent [] (Cof.join [Cof.eq r s; phi]) |>>
        function
        | true ->
          reduce_to @<< do_ap2 bdy (D.dim_to_con s) D.Prf
        | false ->
          ret `Done
      end
    | D.Box (r, s, phi, sides, cap) ->
      begin
        test_sequent [] (Cof.eq r s) |>>
        function
        | true ->
          reduce_to @<< do_sub_out cap
        | false ->
          test_sequent [] phi |>>
          function
          | true ->
            reduce_to @<< do_ap sides D.Prf
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
          dispatch_rigid_coe abs r s con |>>
          function
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
            dispatch_rigid_hcom code r s phi bdy |>>
            function
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
        reduce_to @<< inst_tm_clo clo D.Prf
      | false ->
        whnf_cut cut |>> function
        | `Done ->
          ret `Done
        | `Reduce con ->
          reduce_to @<< do_sub_out con
    end
  | D.Split (tp, branches) ->
    let rec go =
      function
      | [] -> ret `Done
      | (phi, clo) :: branches ->
        test_sequent [] phi |>> function
        | true ->
          reduce_to @<< inst_tm_clo clo D.Prf
        | false ->
          go branches
    in
    go branches

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
  | D.El con ->
    begin
      whnf_con con |>>
      function
      | `Done -> ret `Done
      | `Reduce con -> ret @@ `Reduce (D.El con)
    end
  | D.UnfoldEl cut ->
    begin
      whnf_cut cut |>>
      function
      | `Done -> ret `Done
      | `Reduce con ->
        let+ tp = unfold_el con in
        `Reduce tp
    end
  | D.TpHCom (r, s, phi, bdy) ->
    begin
      Cof.join [Cof.eq r s; phi] |> test_sequent [] |>>
      function
      | true ->
        let* code = do_ap2 bdy (D.dim_to_con s) D.Prf in
        begin
          whnf_tp @@ D.El code |>>
          function
          | `Done -> ret @@ `Reduce (D.El code)
          | `Reduce tp -> ret @@ `Reduce tp
        end
      | false ->
        ret `Done
    end
  | tp ->
    ret `Done

and do_nat_elim (mot : D.con) zero (suc : D.con) n : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match n with
  | D.Zero ->
    ret zero
  | D.Suc n ->
    let* v = do_nat_elim mot zero suc n in
    do_ap2 suc n v
  | D.Cut {cut} ->
    let+ fib = do_ap mot n  in
    cut_frm ~tp:(D.El fib) ~cut @@
    D.KNatElim (mot, zero, suc)
  | D.FHCom (`Nat, r, s, phi, bdy) ->
    (* bdy : (i : 𝕀) (_ : [_]) → nat *)
    splice_tm @@
    Splice.foreign mot @@ fun mot ->
    Splice.foreign_dim r @@ fun r ->
    Splice.foreign_dim s @@ fun s ->
    Splice.foreign_cof phi @@ fun phi ->
    Splice.foreign bdy @@ fun bdy ->
    Splice.foreign zero @@ fun zero ->
    Splice.foreign suc @@ fun suc ->
    Splice.term @@
    let fam =
      TB.lam @@ fun i ->
      let fhcom =
        TB.el_out @@
        TB.hcom TB.code_nat r i phi @@
        TB.lam @@ fun j ->
        TB.lam @@ fun prf ->
        TB.el_in @@ TB.ap bdy [j; prf]
      in
      TB.ap mot [fhcom]
    in
    let bdy' =
      TB.lam @@ fun i ->
      TB.lam @@ fun prf ->
      TB.nat_elim mot zero suc @@ TB.ap bdy [i; prf]
    in
    TB.com fam r s phi bdy'
  | _ ->
    Format.eprintf "bad nat-elim: %a@." D.pp_con n;
    CM.throw @@ NbeFailed "Not a number"

and cut_frm ~tp ~cut frm =
  D.Cut {tp; cut = D.push frm cut}

and inst_tp_clo : D.tp_clo -> D.con -> D.tp CM.m =
  fun clo x ->
  match clo with
  | TpClo (bdy, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@
    eval_tp bdy

and inst_tm_clo : D.tm_clo -> D.con -> D.con CM.m =
  fun clo x ->
  match clo with
  | D.Clo (bdy, env) ->
    CM.lift_ev {env with conenv = Snoc (env.conenv, x)} @@
    eval bdy

and inspect_con con =
  let open CM in
  match con with
  | D.Cut {tp; cut} ->
    begin
      whnf_tp tp |>>
      function
      | `Done -> ret con
      | `Reduce tp -> ret @@ D.Cut {tp; cut}
    end
  | _ -> ret con

and whnf_inspect_con con =
  let open CM in
  whnf_con con |>>
  function
  | `Done -> ret con
  | `Reduce con -> ret con


and do_goal_proj con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.GoalRet con -> ret con
    | D.Cut {tp = D.GoalTp (_, tp); cut} ->
      ret @@ cut_frm ~tp ~cut D.KGoalProj
    | _ ->
      CM.throw @@ NbeFailed "do_goal_proj"
  end

and do_fst con : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.Pair (con0, _) -> ret con0
    | D.Cut {tp = D.Sg (base, _, _); cut} ->
      ret @@ cut_frm ~tp:base ~cut D.KFst
    | _ ->
      throw @@ NbeFailed "Couldn't fst argument in do_fst"
  end

and do_snd con : D.con CM.m =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.Pair (_, con1) -> ret con1
    | D.Cut {tp = D.Sg (_, _, fam); cut} ->
      let* fst = do_fst con in
      let+ fib = inst_tp_clo fam fst in
      cut_frm ~tp:fib ~cut D.KSnd
    | _ ->
      throw @@ NbeFailed ("Couldn't snd argument in do_snd")
  end


and do_ap2 f a b =
  let open CM in
  let* fa = do_ap f a in
  do_ap fa b


and do_ap con a =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.Lam (_, clo) ->
      inst_tm_clo clo a

    | D.Destruct dst ->
      do_destruct dst a

    | D.Cut {tp = D.Pi (base, _, fam); cut} ->
      let+ fib = inst_tp_clo fam a in
      cut_frm ~tp:fib ~cut @@ D.KAp (base, a)

    | con ->
      throw @@ NbeFailed "Not a function in do_ap"
  end

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

and do_sub_out con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.SubIn con ->
      ret con
    | D.Cut {tp = D.Sub (tp, phi, clo); cut} ->
      ret @@ D.Cut {tp; cut = D.SubOut (cut, phi, clo), []}
    | _ ->
      throw @@ NbeFailed "do_sub_out"
  end

and do_el_out con =
  let open CM in
  abort_if_inconsistent D.Abort @@
  begin
    inspect_con con |>>
    function
    | D.ElIn con ->
      ret con
    | D.Cut {tp = D.El con; cut} ->
      let+ tp = unfold_el con in
      cut_frm ~tp ~cut D.KElOut
    | D.Cut {tp; cut} ->
      Format.eprintf "bad: %a / %a@." D.pp_tp tp D.pp_con con;
      throw @@ NbeFailed "do_el_out"
    | _ ->
      Format.eprintf "bad el/out: %a@." D.pp_con con;
      throw @@ NbeFailed "do_el_out"
  end

and unfold_el : D.con -> D.tp CM.m =
  let open CM in
  fun con ->
    abort_if_inconsistent D.TpAbort @@
    begin
      inspect_con con |>>
      function

      | D.Cut {cut} ->
        ret @@ D.UnfoldEl cut

      | D.CodeNat ->
        ret D.Nat

      | D.CodeUniv ->
        ret D.Univ

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

      | D.FHCom (`Univ, r, s, phi, bdy) ->
        ret @@ D.TpHCom (r, s, phi, bdy)

      | con ->
        CM.throw @@ NbeFailed "unfold_el failed"
    end

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
    | D.CodeUniv ->
      ret @@ `Reduce `CoeUniv
    | D.FHCom (`Univ, _, _, _, _) ->
      ret @@ `Reduce `CoeFHCom
    | D.Cut {cut} ->
      ret `Done
    | _ ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_coe"
  in
  go @<< whnf_inspect_con @<< do_ap line (D.dim_to_con i)

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
      ret @@ `Reduce (`FHCom `Nat)
    | D.CodeUniv ->
      ret @@ `Reduce (`FHCom `Univ)
    | D.FHCom (`Univ, _, _, _, _) ->
      ret @@ `Reduce `HComFHCom
    | D.Cut {cut} ->
      ret @@ `Done cut
    | _ ->
      throw @@ NbeFailed "Invalid arguments to dispatch_rigid_hcom"
  in
  go @<< whnf_inspect_con code

and enact_rigid_coe line r s con tag =
  let open CM in
  abort_if_inconsistent D.Abort @@
  match tag with
  | `CoeNat | `CoeUniv ->
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
  | `CoeFHCom ->
    raise Todo

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
  | `FHCom tag ->
    (* bdy : (i : 𝕀) (_ : [...]) → el(<nat>) *)
    let+ bdy' =
      splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_out @@ TB.ap bdy [i; prf]
    in
    D.ElIn (D.FHCom (tag, r, s, phi, bdy'))
  | `HComFHCom ->
    raise Todo
  | `Done cut ->
    let tp = D.El (D.Cut {tp = D.Univ; cut}) in
    let hd = D.HCom (cut, r, s, phi, bdy) in
    ret @@ D.Cut {tp; cut = hd, []}

and do_rigid_coe (line : D.con) r s con =
  let open CM in
  CM.abort_if_inconsistent D.Abort @@
  let* tag = dispatch_rigid_coe line r s con in
  match tag with
  | `Done ->
    let hd = D.Coe (line, r, s, con) in
    let+ code = do_ap line (D.dim_to_con s) in
    D.Cut {tp = D.El code; cut = hd, []}
  | `Reduce tag ->
    enact_rigid_coe line r s con tag

and do_rigid_hcom code r s phi (bdy : D.con) =
  let open CM in
  CM.abort_if_inconsistent D.Abort @@
  let* tag = dispatch_rigid_hcom code r s phi bdy in
  match tag with
  | `Done cut ->
    let tp = D.El (D.Cut {tp = D.Univ; cut}) in
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

and do_frm con =
  function
  | D.KAp (_, con') -> do_ap con con'
  | D.KFst -> do_fst con
  | D.KSnd -> do_snd con
  | D.KNatElim (mot, case_zero, case_suc) -> do_nat_elim mot case_zero case_suc con
  | D.KGoalProj -> do_goal_proj con
  | D.KElOut -> do_el_out con

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
