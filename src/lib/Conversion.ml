module S = Syntax
module D = Domain
module Sem = Semantics


exception Todo

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

open QuM
open Monad.Notation (QuM)
module MU = Monad.Util (QuM)
open Sem

(* duplicated *)
let top_var tp =
  let+ n = read_local in
  D.mk_var tp @@ n - 1

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
  QuM.abort_if_inconsistent () @@
  let* tp0 = contractum_or tp0 <@> lift_cmp @@ whnf_tp tp0 in
  let* tp1 = contractum_or tp1 <@> lift_cmp @@ whnf_tp tp1 in
  match tp0, tp1 with
  | D.TpAbort, _ | _, D.TpAbort -> ret ()
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
  | D.Univ, D.Univ ->
    ret ()
  | D.GoalTp (lbl0, tp0), D.GoalTp (lbl1, tp1) when lbl0 = lbl1 ->
    equate_tp tp0 tp1
  | D.El con0, D.El con1 ->
    equate_con D.Univ con0 con1
  | D.UnfoldEl cut0, D.UnfoldEl cut1 ->
    equate_cut cut0 cut1
  | D.TpHCom (r0, s0, phi0, bdy0), D.TpHCom (r1, s1, phi1, bdy1) ->
    raise Todo
  | _ ->
    conv_err @@ ExpectedTypeEq (tp0, tp1)

(* Invariant: tp, con0, con1 not necessarily whnf *)
and equate_con tp con0 con1 =
  QuM.abort_if_inconsistent () @@
  let* tp = contractum_or tp <@> lift_cmp @@ whnf_tp tp in
  let* con0 = contractum_or con0 <@> lift_cmp @@ whnf_con con0 in
  let* con1 = contractum_or con1 <@> lift_cmp @@ whnf_con con1 in
  match tp, con0, con1 with
  | D.TpPrf _, _, _ -> ret ()
  | _, D.Abort, _ -> ret ()
  | _, _, D.Abort -> ret ()
  | _, D.Cut {cut = D.Split (_, branches), _}, _
  | _, _, D.Cut {cut = D.Split (_, branches), _} ->
    let phis = List.map (fun (phi, _) -> phi) branches in
    QuM.left_invert_under_cofs [Cof.join phis] @@
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
  | D.Sub (tp, phi, _), _, _ ->
    let* out0 = lift_cmp @@ do_sub_out con0 in
    let* out1 = lift_cmp @@ do_sub_out con1 in
    equate_con tp out0 out1
  | D.El code, _, _ ->
    let* out0 = lift_cmp @@ do_el_out con0 in
    let* out1 = lift_cmp @@ do_el_out con1 in
    let* tp = lift_cmp @@ unfold_el code in
    equate_con tp out0 out1
  | _, D.Zero, D.Zero ->
    ret ()
  | _, D.Suc con0, D.Suc con1 ->
    equate_con tp con0 con1
  | D.TpDim, _, _ ->
    let* r0 = lift_cmp @@ con_to_dim con0 in
    let* r1 = lift_cmp @@ con_to_dim con1 in
    approx_cof Cof.top @@ Cof.eq r0 r1
  | D.TpCof, _, _ ->
    let* phi0 = lift_cmp @@ con_to_cof con0 in
    let* phi1 = lift_cmp @@ con_to_cof con1 in
    equate_cof phi0 phi1
  | _, D.Cut {cut = cut0}, D.Cut {cut = cut1} ->
    equate_cut cut0 cut1
  | _, D.FHCom (`Nat, r0, s0, phi0, bdy0), D.FHCom (`Nat, r1, s1, phi1, bdy1) ->
    let fix_body bdy =
      lift_cmp @@ splice_tm @@
      Splice.foreign bdy @@ fun bdy ->
      Splice.term @@
      TB.lam @@ fun i -> TB.lam @@ fun prf ->
      TB.el_in @@ TB.ap bdy [i; prf]
    in
    let* bdy0' = fix_body bdy0 in
    let* bdy1' = fix_body bdy1 in
    equate_hcom (D.CodeNat, r0, s0, phi0, bdy0') (D.CodeNat, r1, s1, phi1, bdy1')
  | _, D.CodeNat, D.CodeNat ->
    ret ()
  | _, D.CodeUniv, D.CodeUniv ->
    ret ()

  | univ, D.CodePi (base0, fam0), D.CodePi (base1, fam1)
  | univ, D.CodeSg (base0, fam0), D.CodeSg (base1, fam1) ->
    let* _ = equate_con univ base0 base1 in
    let* fam_tp =
      lift_cmp @@
      splice_tp @@
      Splice.foreign base0 @@ fun base ->
      Splice.foreign_tp univ @@ fun univ ->
      Splice.term @@ TB.pi (TB.el base) @@ fun _ -> univ
    in
    equate_con fam_tp fam0 fam1

  | univ, D.CodePath (fam0, bdry0), D.CodePath (fam1, bdry1) ->
    let* famtp =
      lift_cmp @@
      splice_tp @@
      Splice.foreign_tp univ @@ fun univ ->
      Splice.term @@ TB.pi TB.tp_dim @@ fun _ -> univ
    in
    let* _ = equate_con famtp fam0 fam1 in
    let* bdry_tp =
      lift_cmp @@ splice_tp @@
      Splice.foreign fam0 @@ fun fam ->
      Splice.term @@
      TB.pi TB.tp_dim @@ fun i ->
      let phi = TB.boundary i in
      TB.pi (TB.tp_prf phi) @@ fun prf ->
      TB.el @@ TB.ap fam [i]
    in
    equate_con bdry_tp bdry0 bdry1

  | _ ->
    conv_err @@ ExpectedConEq (tp, con0, con1)

(* Invariant: cut0, cut1 are whnf *)
and equate_cut cut0 cut1 =
  QuM.abort_if_inconsistent () @@
  let* () = assert_done_cut cut0 in
  let* () = assert_done_cut cut1 in
  let hd0, sp0 = cut0 in
  let hd1, sp1 = cut1 in
  match hd0, hd1 with
  | D.Split (tp, branches), _
  | _, D.Split (tp, branches) ->
    let phis = List.map (fun (phi, _) -> phi) branches in
    QuM.left_invert_under_cofs [Cof.join phis] @@
    let* con0 = contractum_or (D.Cut {tp; cut = cut0}) <@> lift_cmp @@ whnf_cut cut0 in
    let* con1 = contractum_or (D.Cut {tp; cut = cut1}) <@> lift_cmp @@ whnf_cut cut1 in
    equate_con tp con0 con1
  | _ ->
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
      equate_con (D.El mot_zero) zero_case0 zero_case1
    in
    let* suc_tp =
      lift_cmp @@ Sem.splice_tp @@
      Splice.foreign mot0 @@ fun mot ->
      Splice.term @@
      TB.pi TB.nat @@ fun x ->
      TB.pi (TB.el (TB.ap mot [x])) @@ fun ih ->
      TB.el @@ TB.ap mot [TB.suc x]
    in
    equate_con suc_tp suc_case0 suc_case1
  | D.KGoalProj, D.KGoalProj ->
    ret ()
  | D.KElOut, D.KElOut ->
    ret ()
  | _ ->
    conv_err @@ ExpectedFrmEq (k0, k1)

and assert_done_hd hd =
  let* w = lift_cmp @@ whnf_hd hd in
  match w with
  | `Done -> ret ()
  | _ -> failwith "internal error: assert_done_hd failed"

and assert_done_cut cut =
  let* w = lift_cmp @@ whnf_cut cut in
  match w with
  | `Done -> ret ()
  | _ -> failwith "internal error: assert_done_cut failed"

(* Invariant: hd0, hd1 are whnf *)
and equate_hd hd0 hd1 =
  QuM.abort_if_inconsistent () @@
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
    equate_con (D.El code) con0 con1
  | D.HCom (cut0, r0, s0, phi0, bdy0), D.HCom (cut1, r1, s1, phi1, bdy1) ->
    let code0 = D.Cut {tp = D.Univ; cut = cut0} in
    let code1 = D.Cut {tp = D.Univ; cut = cut1} in
    equate_hcom (code0, r0, s0, phi0, bdy0) (code1, r1, s1, phi1, bdy1)
  | D.SubOut (cut0, _, _), D.SubOut (cut1, _, _) ->
    equate_cut cut0 cut1
  | hd, D.Split (tp, branches)
  | D.Split (tp, branches), hd ->
    let equate_branch (phi, clo) =
      QuM.left_invert_under_cofs [phi] @@
      equate_con tp (D.Cut {tp; cut = hd,[]}) @<< lift_cmp @@ inst_tm_clo clo D.Prf
    in
    MU.iter equate_branch branches
  | D.Cap (r0, s0, phi0, code0, box0), D.Cap (r1, s1, phi1, code1, box1) ->
    let* () = equate_dim r0 r1 in
    let* () = equate_dim s0 s1 in
    let* () = equate_cof phi0 phi1 in
    let* () =
      let* code_tp =
        lift_cmp @@
        Sem.splice_tp @@
        Splice.foreign_dim r0 @@ fun r ->
        Splice.foreign_cof phi0 @@ fun phi ->
        Splice.term @@
        TB.pi TB.tp_dim @@ fun i ->
        TB.pi (TB.tp_prf (TB.join [TB.eq i r; phi])) @@ fun prf ->
        TB.univ
      in
      equate_con code_tp code0 code1
    in
    equate_cut box0 box1
  | _ ->
    conv_err @@ HeadMismatch (hd0, hd1)

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
  equate_con (D.El code0) con0 con1


and equate_cof phi psi =
  let* () = approx_cof phi psi in
  approx_cof psi phi

and approx_cof phi psi =
  CmpM.test_sequent [phi] psi |> lift_cmp |>> function
  | false ->
    conv_err @@ ExpectedSequentTrue ([phi], psi)
  | true ->
    ret ()

let equal_tp tp0 tp1 : [`Ok | `Err of Error.t] quote =
  trap
    begin
      QuM.left_invert_under_current_cof @@
      equate_tp tp0 tp1
    end |>>
  function
  | Error (ConversionError err) -> ret @@ `Err err
  | Error exn -> throw exn
  | Ok _ -> ret `Ok

let equal_cut cut0 cut1 =
  trap
    begin
      QuM.left_invert_under_current_cof @@
      equate_cut cut0 cut1
    end |>>
  function
  | Error (ConversionError err) -> ret @@ `Err err
  | Error exn -> throw exn
  | Ok _ -> ret `Ok

let equal_con tp con0 con1 =
  trap
    begin
      QuM.left_invert_under_current_cof @@
      equate_con tp con0 con1
    end |>>
  function
  | Error (ConversionError err) -> ret @@ `Err err
  | Error exn -> throw exn
  | Ok _ -> ret `Ok
