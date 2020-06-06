module S = Syntax
module D = Domain
module Sem = Semantics


exception Todo
exception CFHM
exception CJHM
exception CCHM

open CoolBasis
open Monads


module Error =
struct
  type t =
    | ExpectedDimEq of D.dim * D.dim
    | ExpectedSequentTrue of D.cof list * D.cof
    | ExpectedTypeEq of D.tp * D.tp
    | ExpectedConEq of D.tp * D.con * D.con
    | ExpectedFrmEq of D.frm * D.frm
    | SpineLengthMismatch of D.frm list * D.frm list
    | HeadMismatch of D.hd * D.hd

  let pp : t Pp.printer =
    fun fmt ->
    function
    | ExpectedDimEq (r,s) ->
      Format.fprintf fmt "Expected %a = %a : dim" D.pp_dim r D.pp_dim s
    | ExpectedSequentTrue (phis, psi) ->
      Format.fprintf fmt "Expected @[%a |- @[%a@]@] true" D.pp_cof (Cof.meet phis) D.pp_cof psi
    | ExpectedTypeEq (tp0, tp1) ->
      Format.fprintf fmt "Expected %a = %a type" D.pp_tp tp0 D.pp_tp tp1
    | ExpectedConEq (tp, con0, con1) ->
      Format.fprintf fmt "Expected %a = %a : %a" D.pp_con con0 D.pp_con con1 D.pp_tp tp
    | ExpectedFrmEq (frm0, frm1) ->
      Format.fprintf fmt "Expected %a = %a" D.pp_frame frm0 D.pp_frame frm1
    | SpineLengthMismatch (sp0, sp1) ->
      Format.fprintf fmt "Spine length mismatch between %a and %a" D.pp_spine sp0 D.pp_spine sp1
    | HeadMismatch (hd0, hd1) ->
      Format.fprintf fmt "Head mismatch between %a and %a" D.pp_hd hd0 D.pp_hd hd1
end

exception ConversionError of Error.t

module Splice = Splice
module TB = TermBuilder

open ConvM
open Monad.Notation (ConvM)
module MU = Monad.Util (ConvM)
open Sem

let conv_err err =
  throw @@ ConversionError err

let equate_dim r s =
  CmpM.test_sequent [] (Cof.eq r s) |> lift_cmp |>> function
  | true ->
    ret ()
  | false ->
    conv_err @@ ExpectedDimEq (r, s)

let contractum_or x =
  function
  | `Done -> x
  | `Reduce y -> y

(* Invariant: tp0 and tp1 not necessarily whnf *)
let rec equate_tp (tp0 : D.tp) (tp1 : D.tp) =
  ConvM.abort_if_inconsistent (ret ()) @@
  let* tp0 = contractum_or tp0 <@> lift_cmp @@ whnf_tp tp0 in
  let* tp1 = contractum_or tp1 <@> lift_cmp @@ whnf_tp tp1 in
  match tp0, tp1 with
  | D.TpSplit branches, _
  | _, D.TpSplit branches ->
    let phis = List.map (fun (phi, _) -> phi) branches in
    ConvM.restrict_ [Cof.join phis] @@
    equate_tp tp0 tp1
  | D.TpDim, D.TpDim | D.TpCof, D.TpCof -> ret ()
  | D.TpPrf phi0, D.TpPrf phi1 ->
    equate_cof phi0 phi1
  | D.Pi (base0, _, fam0), D.Pi (base1, _, fam1)
  | D.Sg (base0, _, fam0), D.Sg (base1, _, fam1) ->
    let* () = equate_tp base0 base1 in
    bind_var_ base0 @@ fun x ->
    let* fib0 = lift_cmp @@ inst_tp_clo fam0 x in
    let* fib1 = lift_cmp @@ inst_tp_clo fam1 x in
    equate_tp fib0 fib1
  | D.Sub (tp0, phi0, clo0), D.Sub (tp1, phi1, clo1) ->
    let* () = equate_tp tp0 tp1 in
    let* () = equate_cof phi0 phi1 in
    bind_var_ (D.TpPrf phi0) @@ fun prf ->
    let* con0 = lift_cmp @@ inst_tm_clo clo0 prf in
    let* con1 = lift_cmp @@ inst_tm_clo clo1 prf in
    equate_con tp0 con0 con1
  | D.Nat, D.Nat
  | D.Circle, D.Circle
  | D.Univ, D.Univ ->
    ret ()
  | D.GoalTp (lbl0, tp0), D.GoalTp (lbl1, tp1) when lbl0 = lbl1 ->
    equate_tp tp0 tp1
  | D.ElStable code0, D.ElStable code1 ->
    equate_stable_code D.Univ code0 code1
  | D.ElCut cut0, D.ElCut cut1 ->
    equate_cut cut0 cut1
  | D.ElUnstable (`HCom (r0, s0, phi0, bdy0)), D.ElUnstable (`HCom (r1, s1, phi1, bdy1)) ->
    let* () = equate_dim r0 r1 in
    let* () = equate_dim s0 s1 in
    let* () = equate_cof phi0 phi1 in
    let* tp_bdy =
      lift_cmp @@
      Sem.splice_tp @@
      Splice.dim r0 @@ fun r ->
      Splice.cof phi0 @@ fun phi ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun _prf ->
      TB.univ
    in
    equate_con tp_bdy bdy0 bdy1
  | D.ElUnstable (`V (r0, pcode0, code0, pequiv0)), D.ElUnstable (`V (r1, pcode1, code1, pequiv1)) ->
    equate_v_data (r0, pcode0, code0, pequiv0) (r1, pcode1, code1, pequiv1)
  | _ ->
    conv_err @@ ExpectedTypeEq (tp0, tp1)

and equate_stable_code univ code0 code1 =
  match code0, code1 with
  | `Nat, `Nat | `Circle, `Circle | `Univ, `Univ -> ret ()
  | `Pi (base0, fam0), `Pi (base1, fam1)
  | `Sg (base0, fam0), `Sg (base1, fam1) ->
    let* _ = equate_con univ base0 base1 in
    let* fam_tp =
      lift_cmp @@
      splice_tp @@
      Splice.con base0 @@ fun base ->
      Splice.tp univ @@ fun univ ->
      Splice.term @@ TB.pi (TB.el base) @@ fun _ -> univ
    in
    equate_con fam_tp fam0 fam1

  | `Path (fam0, bdry0), `Path (fam1, bdry1) ->
    let* famtp =
      lift_cmp @@
      splice_tp @@
      Splice.tp univ @@ fun univ ->
      Splice.term @@ TB.pi TB.tp_dim @@ fun _ -> univ
    in
    let* _ = equate_con famtp fam0 fam1 in
    let* bdry_tp =
      lift_cmp @@ splice_tp @@
      Splice.con fam0 @@ fun fam ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      let phi = TB.boundary i in
      TB.pi (TB.tp_prf phi) @@ fun _prf ->
      TB.el @@ TB.ap fam [i]
    in
    equate_con bdry_tp bdry0 bdry1
  | code0, code1 ->
    conv_err @@ ExpectedConEq (univ, D.StableCode code0, D.StableCode code1)

(* Invariant: tp, con0, con1 not necessarily whnf *)
and equate_con tp con0 con1 =
  ConvM.abort_if_inconsistent (ret ()) @@
  let* tp = contractum_or tp <@> lift_cmp @@ whnf_tp tp in
  let* con0 = contractum_or con0 <@> lift_cmp @@ whnf_con ~style:`UnfoldAll con0 in
  let* con1 = contractum_or con1 <@> lift_cmp @@ whnf_con ~style:`UnfoldAll con1 in
  match tp, con0, con1 with
  | D.TpPrf _, _, _ -> ret ()
  | D.TpSplit branches, _, _ ->
    let phis = List.map (fun (phi, _) -> phi) branches in
    ConvM.restrict_ [Cof.join phis] @@
    equate_con tp con0 con1
  | _, D.Split branches, _
  | _, _, D.Split branches ->
    let phis = List.map (fun (phi, _) -> phi) branches in
    ConvM.restrict_ [Cof.join phis] @@
    equate_con tp con0 con1
  | D.Pi (base, _, fam), _, _ ->
    bind_var_ base @@ fun x ->
    let* fib = lift_cmp @@ inst_tp_clo fam x in
    let* ap0 = lift_cmp @@ do_ap con0 x in
    let* ap1 = lift_cmp @@ do_ap con1 x in
    equate_con fib ap0 ap1
  | D.Sg (base, _, fam), _, _ ->
    let* fst0 = lift_cmp @@ do_fst con0 in
    let* fst1 = lift_cmp @@ do_fst con1 in
    let* () = equate_con base fst0 fst1 in
    let* fib = lift_cmp @@ inst_tp_clo fam fst0 in
    let* snd0 = lift_cmp @@ do_snd con0 in
    let* snd1 = lift_cmp @@ do_snd con1 in
    equate_con fib snd0 snd1
  | D.GoalTp (_, tp), _, _ ->
    let* con0 = lift_cmp @@ do_goal_proj con0 in
    let* con1 = lift_cmp @@ do_goal_proj con1 in
    equate_con tp con0 con1
  | D.Sub (tp, _phi, _), _, _ ->
    let* out0 = lift_cmp @@ do_sub_out con0 in
    let* out1 = lift_cmp @@ do_sub_out con1 in
    equate_con tp out0 out1
  | D.ElStable code, _, _ ->
    let* out0 = lift_cmp @@ do_el_out con0 in
    let* out1 = lift_cmp @@ do_el_out con1 in
    let* tp = lift_cmp @@ unfold_el code in
    equate_con tp out0 out1
  | _, D.Zero, D.Zero ->
    ret ()
  | _, D.Suc con0, D.Suc con1 ->
    equate_con tp con0 con1
  | _, D.Base, D.Base ->
    ret ()
  | _, D.Loop r0, D.Loop r1 ->
    equate_dim r0 r1
  | D.TpDim, _, _ ->
    let* r0 = lift_cmp @@ con_to_dim con0 in
    let* r1 = lift_cmp @@ con_to_dim con1 in
    approx_cof Cof.top @@ Cof.eq r0 r1
  | D.TpCof, _, _ ->
    let* phi0 = lift_cmp @@ con_to_cof con0 in
    let* phi1 = lift_cmp @@ con_to_cof con1 in
    equate_cof phi0 phi1
  | _, D.Cut {cut = cut0; _}, D.Cut {cut = cut1; _} ->
    equate_cut cut0 cut1
  | _, D.FHCom (`Nat, r0, s0, phi0, bdy0), D.FHCom (`Nat, r1, s1, phi1, bdy1) ->
    let fix_body bdy =
      lift_cmp @@ splice_tm @@
      Splice.con bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let* bdy0' = fix_body bdy0 in
    let* bdy1' = fix_body bdy1 in
    equate_hcom (D.StableCode `Nat, r0, s0, phi0, bdy0') (D.StableCode `Nat, r1, s1, phi1, bdy1')
  | _, D.FHCom (`Circle, r0, s0, phi0, bdy0), D.FHCom (`Circle, r1, s1, phi1, bdy1) ->
    let fix_body bdy =
      lift_cmp @@ splice_tm @@
      Splice.con bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let* bdy0' = fix_body bdy0 in
    let* bdy1' = fix_body bdy1 in
    equate_hcom (D.StableCode `Circle, r0, s0, phi0, bdy0') (D.StableCode `Circle, r1, s1, phi1, bdy1')
  | univ, D.StableCode code0, D.StableCode code1 ->
    equate_stable_code univ code0 code1

  | _, D.UnstableCode (`V (r0, pcode0, code0, pequiv0)), D.UnstableCode (`V (r1, pcode1, code1, pequiv1)) ->
    equate_v_data (r0, pcode0, code0, pequiv0) (r1, pcode1, code1, pequiv1)


  | D.ElUnstable (`HCom (r, s, phi, bdy)) as hcom_tp, _, _ ->
    let* cap0 = lift_cmp @@ Sem.do_rigid_cap r s phi bdy con0 in
    let* cap1 = lift_cmp @@ Sem.do_rigid_cap r s phi bdy con1 in
    let* code_cap = lift_cmp @@ Sem.do_ap2 bdy (D.dim_to_con r) D.Prf in
    let* tp_cap = lift_cmp @@ do_el code_cap in
    let* () = equate_con tp_cap cap0 cap1 in
    ConvM.restrict_ [phi] @@
    equate_con hcom_tp con0 con1

  | D.ElUnstable (`V (r, pcode, code, pequiv)) as v_tp, _, _ ->
    let* () = ConvM.restrict_ [Cof.eq r D.Dim0] @@ equate_con v_tp con0 con1 in
    let* proj0 = lift_cmp @@ Sem.do_rigid_vproj r pcode code pequiv con0 in
    let* proj1 = lift_cmp @@ Sem.do_rigid_vproj r pcode code pequiv con1 in
    let* tp_proj = lift_cmp @@ do_el code in
    equate_con tp_proj proj0 proj1

  | _ ->
    Format.eprintf "failed: %a, %a@." D.pp_con con0 D.pp_con con1;
    conv_err @@ ExpectedConEq (tp, con0, con1)

(* Invariant: cut0, cut1 are whnf *)
and equate_cut cut0 cut1 =
  ConvM.abort_if_inconsistent (ret ()) @@
  let* () = assert_done_cut cut0 in
  let* () = assert_done_cut cut1 in
  let hd0, sp0 = cut0 in
  let hd1, sp1 = cut1 in
  let* () = equate_hd hd0 hd1 in
  equate_spine sp0 sp1

(* Invariant: sp0, sp1 are whnf *)
and equate_spine sp0 sp1 =
  let exception Mismatch in
  let rec go sp0 sp1 =
    match sp0, sp1 with
    | [], [] -> ret ()
    | k0 :: sp0, k1 :: sp1 ->
      let* () = equate_frm k0 k1 in
      go sp0 sp1
    | _ ->
      raise Mismatch
  in
  try go sp0 sp1 with
  | Mismatch ->
    conv_err @@ Error.SpineLengthMismatch (sp0, sp1)

(* Invariant: k0, k1 are whnf *)
and equate_frm k0 k1 =
  match k0, k1 with
  | D.KFst, D.KFst
  | D.KSnd, D.KSnd ->
    ret ()
  | D.KAp (tp0, con0), D.KAp (tp1, con1) ->
    let* () = equate_tp tp0 tp1 in
    equate_con tp0 con0 con1
  | D.KNatElim (mot0, zero_case0, suc_case0), D.KNatElim (mot1, zero_case1, suc_case1) ->
    let* mot_tp =
      lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.nat @@ fun _ -> TB.univ
    in
    let* () = equate_con mot_tp mot0 mot1 in
    let* () =
      let* mot_zero = lift_cmp @@ do_ap mot0 D.Zero in
      let* tp_mot_zero = lift_cmp @@ do_el mot_zero in
      equate_con tp_mot_zero zero_case0 zero_case1
    in
    let* suc_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.con mot0 @@ fun mot ->
      Splice.term @@
      TB.pi TB.nat @@ fun x ->
      TB.pi (TB.el (TB.ap mot [x])) @@ fun _ih ->
      TB.el @@ TB.ap mot [TB.suc x]
    in
    equate_con suc_tp suc_case0 suc_case1
  | D.KCircleElim (mot0, base_case0, loop_case0), D.KCircleElim (mot1, base_case1, loop_case1) ->
    let* mot_tp =
      lift_cmp @@ Sem.splice_tp @@ Splice.term @@
      TB.pi TB.circle @@ fun _ -> TB.univ
    in
    let* () = equate_con mot_tp mot0 mot1 in
    let* () =
      let* mot_base = lift_cmp @@ do_ap mot0 D.Base in
      let* tp_mot_base = lift_cmp @@ do_el mot_base in
      equate_con tp_mot_base base_case0 base_case1
    in
    let* loop_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.con mot0 @@ fun mot ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun x ->
      TB.el @@ TB.ap mot [TB.loop x]
    in
    equate_con loop_tp loop_case0 loop_case1
  | D.KGoalProj, D.KGoalProj ->
    ret ()
  | D.KElOut, D.KElOut ->
    ret ()
  | _ ->
    conv_err @@ ExpectedFrmEq (k0, k1)

and assert_done_hd hd =
  let* w = lift_cmp @@ whnf_hd ~style:`UnfoldAll hd in
  match w with
  | `Done -> ret ()
  | _ -> failwith "internal error: assert_done_hd failed"

and assert_done_cut cut =
  let* w = lift_cmp @@ whnf_cut ~style:`UnfoldAll cut in
  match w with
  | `Done -> ret ()
  | _ -> failwith "internal error: assert_done_cut failed"

(* Invariant: hd0, hd1 are whnf *)
and equate_hd hd0 hd1 =
  ConvM.abort_if_inconsistent (ret ()) @@
  let* () = assert_done_hd hd0 in
  let* () = assert_done_hd hd1 in
  match hd0, hd1 with
  | D.Global sym0, D.Global sym1 when Symbol.equal sym0 sym1 -> ret ()
  | D.Var lvl0, D.Var lvl1 when lvl0 = lvl1 -> ret ()
  | D.Coe (abs0, r0, s0, con0), D.Coe (abs1, r1, s1, con1) ->
    let* () = equate_dim r0 r1 in
    let* () = equate_dim s0 s1 in
    let* () =
      bind_var_ D.TpDim @@ fun i ->
      let* code0 = lift_cmp @@ do_ap abs0 i in
      let* code1 = lift_cmp @@ do_ap abs1 i in
      equate_con D.Univ code0 code1
    in
    let* code = lift_cmp @@ do_ap abs0 @@ D.dim_to_con r0 in
    let* tp_code = lift_cmp @@ do_el code in
    equate_con tp_code con0 con1
  | D.UnstableCut (cut0, ufrm0), D.UnstableCut (cut1, ufrm1) ->
    equate_unstable_cut (cut0, ufrm0) (cut1, ufrm1)
  | _ ->
    conv_err @@ HeadMismatch (hd0, hd1)

and equate_unstable_cut (cut0, ufrm0) (cut1, ufrm1) =
  match ufrm0, ufrm1 with
  | D.KHCom (r0, s0, phi0, bdy0), D.KHCom (r1, s1, phi1, bdy1) ->
    let code0 = D.Cut {tp = D.Univ; cut = cut0} in
    let code1 = D.Cut {tp = D.Univ; cut = cut1} in
    equate_hcom (code0, r0, s0, phi0, bdy0) (code1, r1, s1, phi1, bdy1)
  | D.KSubOut _, D.KSubOut _ ->
    equate_cut cut0 cut1
  | D.KCap (r0, s0, phi0, code0), D.KCap (r1, s1, phi1, code1) ->
    let* () = equate_dim r0 r1 in
    let* () = equate_dim s0 s1 in
    let* () = equate_cof phi0 phi1 in
    let* () =
      let* code_tp =
        lift_cmp @@
        Sem.splice_tp @@
        Splice.dim r0 @@ fun r ->
        Splice.cof phi0 @@ fun phi ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun _prf ->
        TB.univ
      in
      equate_con code_tp code0 code1
    in
    equate_cut cut0 cut1
  | D.KVProj (r0, pcode0, code0, pequiv0), D.KVProj (r1, pcode1, code1, pequiv1) ->
    let* () = equate_v_data (r0, pcode0, code0, pequiv0) (r1, pcode1, code1, pequiv1) in
    equate_cut cut0 cut1
  | _ ->
    conv_err @@ HeadMismatch (D.UnstableCut (cut0, ufrm0), D.UnstableCut (cut1, ufrm1))

and equate_v_data (r0, pcode0, code0, pequiv0) (r1, pcode1, code1, pequiv1) =
  let* () = equate_dim r0 r1 in
  let* () =
    let pcode_tp = D.Pi (D.TpPrf (Cof.eq r0 D.Dim0), `Anon, D.const_tp_clo D.Univ) in
    equate_con pcode_tp pcode0 pcode1
  in
  let* () = equate_con D.Univ code0 code1 in
  let* pequiv_tp =
    lift_cmp @@
    Sem.splice_tp @@
    Splice.Macro.tp_pequiv_in_v ~r:r0 ~pcode:pcode0 ~code:code0
  in
  equate_con pequiv_tp pequiv0 pequiv1

and equate_hcom (code0, r0, s0, phi0, bdy0) (code1, r1, s1, phi1, bdy1) =
  let* () = equate_con D.Univ code0 code1 in
  let* () = equate_dim r0 r1 in
  let* () = equate_dim s0 s1 in
  let* () = equate_cof phi0 phi1 in
  bind_var_ D.TpDim @@ fun i ->
  let* i_dim = lift_cmp @@ con_to_dim i in
  bind_var_ (D.TpPrf (Cof.join [Cof.eq i_dim r0; phi0])) @@ fun prf ->
  let* con0 = lift_cmp @@ do_ap2 bdy0 i prf in
  let* con1 = lift_cmp @@ do_ap2 bdy1 i prf in
  let* tp = lift_cmp @@ do_el code0 in
  equate_con tp con0 con1


and equate_cof phi psi =
  let* () = approx_cof phi psi in
  approx_cof psi phi

and approx_cof phi psi =
  CmpM.test_sequent [phi] psi |> lift_cmp |>> function
  | false ->
    conv_err @@ ExpectedSequentTrue ([phi], psi)
  | true ->
    ret ()

(* This is extremely low-ch'i.
 * There should be a generic error-trapping function in src/basis/Monad. *)
let trap_err (m : unit ElabM.m) : [`Ok | `Err of Error.t] ElabM.m =
  ElabM.bind (ElabM.trap m) @@ function
  | Error (ConversionError err) -> ElabM.ret @@ `Err err
  | Error exn -> ElabM.throw exn
  | Ok _ -> ElabM.ret `Ok
