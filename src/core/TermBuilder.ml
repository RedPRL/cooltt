open Basis
open Bwd
open Cubical

open CodeUnit

exception CFHM
exception CCHM
exception CJHM

module S = Syntax

module M : sig
  include Monad.S
  val scope : (S.t m -> 'a m) -> 'a m
  val run : tplen:int -> conlen:int-> 'a m -> 'a
  val lvl : int -> S.t m
  val tplvl : int -> S.tp m

  val test : S.t m -> unit
end =
struct
  type local = {tplen : int; conlen : int}
  type token = {lvl : int}

  type 'a m = local -> 'a

  let ret a : _ m =
    fun _ -> a

  let bind m f : _ m =
    fun loc ->
    let x = m loc in
    f x loc

  let var tok : _ m =
    fun loc ->
    S.Var (loc.conlen - tok.lvl - 1)

  let tpvar tok : _ m =
    fun loc ->
    S.TpVar (loc.tplen - tok.lvl - 1)

  let lvl l = var {lvl = l}
  let tplvl l = tpvar {lvl = l}

  let scope (k : S.t m -> 'a m) : 'a m =
    fun loc ->
    let tok = {lvl = loc.conlen} in
    k (var tok) {loc with conlen = loc.conlen + 1}

  let run ~tplen ~conlen m =
    m {tplen; conlen}

  let test m =
    let tm = run ~tplen:0 ~conlen:0 m in
    Format.printf
      "@[<v>Testing:@ %a@]@."
      (S.pp Pp.Env.emp) tm
end


include M
open Monad.Notation (M)
module MU = Monad.Util (M)

type 'a b = S.t m -> 'a m

let el_in m : _ m =
  let+ tm = m in
  S.ElIn tm

let tp_locked_prf mphi : _ m =
  let+ phi = mphi in
  S.TpLockedPrf phi

let locked_prf_in mprf : _ m =
  let+ prf = mprf in
  S.LockedPrfIn prf

let locked_prf_unlock mtp ~cof ~prf ~bdy =
  let+ tp = mtp
  and+ cof = cof
  and+ prf = prf
  and+ bdy = bdy in
  S.LockedPrfUnlock {tp; cof; prf; bdy}


let el_out m : _ m =
  let+ tm = m in
  S.ElOut tm

let lam ?(ident = `Anon) mbdy : _ m =
  scope @@ fun var ->
  let+ bdy = mbdy var in
  S.Lam (ident, bdy)

let rec ap m0 ms : _ m =
  match ms with
  | [] -> m0
  | m1 :: ms ->
    let* x0 = m0 in
    let* x1 = m1 in
    ap (ret (S.Ap (x0, x1))) ms

let coe mline mr ms mbdy =
  let+ line = mline
  and+ r = mr
  and+ s = ms
  and+ bdy = mbdy in
  S.Coe (line, r, s, bdy)


let hcom mcode mr ms mphi mbdy =
  let+ code = mcode
  and+ r = mr
  and+ s = ms
  and+ phi = mphi
  and+ bdy = mbdy in
  S.HCom (code, r, s, phi, bdy)

let com mline mr ms mphi mbdy =
  let+ line = mline
  and+ r = mr
  and+ s = ms
  and+ phi = mphi
  and+ bdy = mbdy in
  S.Com (line, r, s, phi, bdy)


let let_ ?(ident = `Anon) m k : _ m =
  let+ t = m
  and+ bdy = scope k in
  S.Let (t, ident, bdy)

let pair m0 m1 =
  let+ x0 = m0
  and+ x1 = m1 in
  S.Pair (x0, x1)

let fst m =
  let+ x = m in
  S.Fst x

let snd m =
  let+ x = m in
  S.Snd x

let tm_abort =
  ret @@ S.tm_abort

let const (m : 'a m) : 'a b =
  fun _ -> m


let cof_split mbranches =
  let mphis, mtms = List.split mbranches in
  let+ phis = MU.commute_list mphis
  and+ tms = MU.map scope @@ List.map const mtms in
  S.CofSplit (List.combine phis tms)

let tp_cof_split (mbranches : (S.t m * S.tp m) list)=
  let mphis, mtps = List.split mbranches in
  let+ phis = MU.commute_list mphis
  and+ tps = MU.map scope @@ List.map const mtps in
  S.TpCofSplit (List.combine phis tps)

let sub_out mtm =
  let+ tm = mtm in
  S.SubOut tm

let sub_in mtm =
  let+ tm = mtm in
  S.SubIn tm

let univ : _ m =
  ret S.Univ

let nat : _ m =
  ret S.Nat

let code_nat =
  ret S.CodeNat

let nat_elim mmot mzero msuc mscrut =
  let+ mot = mmot
  and+ zero = mzero
  and+ suc = msuc
  and+ scrut = mscrut in
  S.NatElim (mot, zero, suc, scrut)


let zero =
  ret S.Zero

let suc m =
  let+ x = m in
  S.Suc x

let circle : _ m =
  ret S.Circle

let code_circle =
  ret S.CodeCircle

let circle_elim mmot mbase mloop mscrut =
  let+ mot = mmot
  and+ base = mbase
  and+ loop = mloop
  and+ scrut = mscrut in
  S.CircleElim (mot, base, loop, scrut)

let base =
  ret S.Base

let loop m =
  let+ x = m in
  S.Loop x

let pi ?(ident = `Anon) mbase mfam : _ m =
  let+ base = mbase
  and+ fam = scope mfam in
  S.Pi (base, ident, fam)

let sg ?(ident = `Anon) mbase mfam : _ m =
  let+ base = mbase
  and+ fam = scope mfam in
  S.Sg (base, ident, fam)

let code_pi mbase mfam : _ m =
  let+ base = mbase
  and+ fam = mfam in
  S.CodePi (base, fam)

let code_sg mbase mfam : _ m =
  let+ base = mbase
  and+ fam = mfam in
  S.CodeSg (base, fam)

let code_path mfam mbdry : _ m =
  let+ fam = mfam
  and+ bdry = mbdry in
  S.CodeExt (1, fam, `Global (S.Lam (`Anon, S.Cof (Cof.Join [S.Cof (Cof.Eq (S.Var 0, S.Dim0)); S.Cof (Cof.Eq (S.Var 0, S.Dim1))]))), bdry)

let code_v mr mpcode mcode mpequiv : _ m=
  let+ r = mr
  and+ pcode = mpcode
  and+ code = mcode
  and+ pequiv = mpequiv in
  S.CodeV (r, pcode, code, pequiv)

let sub mbase mphi mbdry =
  let+ base = mbase
  and+ phi = mphi
  and+ bdry = scope mbdry in
  S.Sub (base, phi, bdry)

let el mcode : _ m =
  let+ code = mcode in
  S.El code

let tp_prf mphi =
  let+ phi = mphi in
  S.TpPrf phi

let prf =
  ret S.Prf


let eq mr ms =
  let+ r = mr
  and+ s = ms in
  S.Cof (Cof.Eq (r, s))

let join mphis =
  let+ phis = MU.commute_list mphis in
  S.Cof (Cof.Join phis)

let meet mphis =
  let+ phis = MU.commute_list mphis in
  S.Cof (Cof.Meet phis)

let forall mphi =
  let+ phi = scope mphi in
  S.ForallCof phi

let tp_dim = ret S.TpDim
let tp_cof = ret S.TpCof
let dim0 = ret S.Dim0
let dim1 = ret S.Dim1

let cube n mfam : _ m =
  let rec go acc n =
    if n = 0 then
      mfam @@ Bwd.to_list acc
    else
      pi tp_dim @@ fun i ->
      go (Snoc (acc, i)) (n - 1)
  in
  go Emp n

let nlam n mbdy : _ m =
  let rec go acc n =
    if n = 0 then
      mbdy @@ Bwd.to_list acc
    else
      lam @@ fun i ->
      go (Snoc (acc, i)) (n - 1)
  in
  go Emp n


let boundary mr =
  join [eq mr dim0; eq mr dim1]

let box mr ms mphi msides mcap =
  let+ r = mr
  and+ s = ms
  and+ phi = mphi
  and+ sides = msides
  and+ cap = mcap in
  S.Box (r, s, phi, sides, cap)

let cap mr ms mphi mcode mbox =
  let+ r = mr
  and+ s = ms
  and+ phi = mphi
  and+ code = mcode
  and+ box = mbox in
  S.Cap (r, s, phi, code, box)

let vin mr mpequiv mpivot mbase =
  let+ r = mr
  and+ pequiv = mpequiv
  and+ pivot = mpivot
  and+ base = mbase in
  S.VIn (r, pequiv, pivot, base)

let vproj mr mpcode mcode mpequiv mv =
  let+ r = mr
  and+ pcode = mpcode
  and+ code = mcode
  and+ pequiv = mpequiv
  and+ v = mv in
  S.VProj (r, pcode, code, pequiv, v)

let code_path' mfam ml mr : _ m =
  code_path mfam @@ lam @@ fun i ->
  lam @@ fun _ ->
  cof_split
    [eq i dim0, ml;
     eq i dim1, mr]


module Equiv : sig
  val code_is_contr : S.t m -> S.t m
  val code_fiber : S.t m -> S.t m -> S.t m -> S.t m -> S.t m
  val code_equiv : S.t m -> S.t m -> S.t m
  val equiv_fwd : S.t m -> S.t m
  val equiv_inv : S.t m -> S.t m -> S.t m
  val equiv_inv_path : S.t m -> S.t m -> S.t m -> S.t m
end =
struct
  let code_is_contr code =
    code_sg code @@ lam @@ fun x ->
    code_pi code @@ lam @@ fun y ->
    code_path' (lam @@ fun _ -> code) x y

  let code_fiber code_a code_b f b =
    code_sg code_a @@ lam @@ fun a ->
    code_path' (lam @@ fun _ -> code_b) (ap f [a]) b

  let code_equiv code_a code_b =
    code_sg (code_pi code_a @@ lam @@ fun _ -> code_b) @@ lam @@ fun f ->
    code_pi code_b @@ lam @@ fun y ->
    code_is_contr @@ code_fiber code_a code_b (el_out f) y

  let equiv_fwd equiv =
    el_out @@ fst @@ el_out equiv

  (* CJHM CCHM names *)
  let equiv_fiber_contr equiv y =
    ap (el_out @@ snd @@ el_out equiv) [y]

  (* CJHM CCHM names *)
  let equiv_inv equiv y =
    fst @@ el_out @@ equiv_fiber_contr equiv y

  (* CJHM CCHM names *)
  let equiv_inv_path equiv y p =
    ap (el_out @@ snd @@ el_out @@ equiv_fiber_contr equiv y) [p]
end

module Kan =
struct
  type coe = r:S.t m -> r':S.t m -> bdy:S.t m -> S.t m
  type hcom = r:S.t m -> r':S.t m -> phi:S.t m -> bdy:S.t m -> S.t m

  let coe_pi ~base_line ~fam_line ~r ~r' ~bdy : _ m =
    el_in @@
    lam @@ fun arg ->
    let_ (lam @@ fun i -> coe base_line r' i arg) @@ fun coe_base_line ->
    let fib_line = lam @@ fun i -> ap fam_line [i; ap coe_base_line [i]] in
    coe fib_line r r' @@
    ap (el_out bdy) [ap coe_base_line [r]]

  let hcom_pi ~fam ~r ~r' ~phi ~bdy : _ m =
    el_in @@
    lam @@ fun arg ->
    let tfib = ap fam [arg] in
    hcom tfib r r' phi @@
    lam @@ fun i ->
    lam @@ fun prf ->
    ap (el_out (ap bdy [i; prf])) [arg]

  let coe_sg ~base_line ~fam_line ~r ~r' ~bdy : _ m =
    let fst_line = lam @@ fun i -> coe base_line r i @@ fst @@ el_out bdy in
    let fib_line = lam @@ fun i -> ap fam_line [i; ap fst_line [i]] in
    el_in @@
    pair
      (ap fst_line [r'])
      (coe fib_line r r' @@ snd @@ el_out bdy)

  let hcom_sg ~base ~fam ~r ~r' ~phi ~bdy : _ m =
    let p0_line =
      lam @@ fun i ->
      hcom base r i phi @@
      lam @@ fun j ->
      lam @@ fun prf ->
      fst @@ el_out @@ ap bdy [j; prf]
    in
    let p0 = ap p0_line [r'] in
    let fib_line =
      lam @@ fun i ->
      ap fam [ap p0_line [i]]
    in
    let p1 =
      com fib_line r r' phi @@
      lam @@ fun i ->
      lam @@ fun prf ->
      snd @@ el_out @@ ap bdy [i; prf]
    in
    el_in @@
    pair p0 p1

  let coe_ext ~n ~cof ~fam_line ~bdry_line ~r ~r' ~bdy =
    el_in @@
    nlam n @@ fun js ->
    sub_in @@
    let_ (ap cof js) @@ fun cof_js ->
    com (lam @@ fun i -> ap fam_line @@ i :: js) r r' cof_js @@
    lam @@ fun i ->
    lam @@ fun _ ->
    cof_split
      [cof_js, ap bdry_line @@ i :: js @ [prf]
      ; eq i r, sub_out @@ ap (el_out bdy) js]

  let hcom_ext ~n ~cof ~fam ~bdry ~r ~r' ~phi ~bdy =
    el_in @@
    nlam n @@ fun js ->
    sub_in @@
    let_ (ap cof js) @@ fun cof_js ->
    let_ (ap fam js) @@ fun fam_js ->
    hcom fam_js r r' (join [phi; cof_js]) @@
    lam @@ fun k ->
    lam @@ fun _p ->
    cof_split
      [ cof_js, ap bdry @@ js @ [prf]
      ; join [phi; eq k r], sub_out @@ ap (el_out (ap bdy [k; prf])) js
      ]

  module V :
  sig
    type vcode = {r : S.t m; pcode : S.t m; code : S.t m; pequiv : S.t m}
    val hcom_v : v:vcode -> r:S.t m -> r':S.t m -> phi:S.t m -> bdy:S.t m -> S.t m
    val coe_v : v:vcode -> r:S.t m -> r':S.t m -> bdy:S.t m -> S.t m
  end =
  struct
    type vcode = {r : S.t m; pcode : S.t m; code : S.t m; pequiv : S.t m}

    let hcom_v ~(v : vcode) ~(r : S.t m) ~(r' : S.t m) ~(phi : S.t m) ~(bdy : S.t m) : S.t m =
      let_ ~ident:(`Machine "O")
        begin
          lam ~ident:(`Machine "X") @@ fun x ->
          lam ~ident:(`Machine "N") @@ fun n ->
          lam ~ident:(`Machine "i") @@ fun i ->
          hcom x r i phi n
        end
      @@ fun o_tilde ->
      let_ ~ident:(`Machine "P")
        begin
          lam ~ident:(`Machine "i") @@ fun i ->
          lam @@ fun _ ->
          cof_split
            [join [eq i r; phi], vproj v.r v.pcode v.code v.pequiv @@ ap bdy [i; prf];
             eq v.r dim0, ap (Equiv.equiv_fwd (ap v.pequiv [prf])) [ap o_tilde [ap v.pcode [prf]; bdy; i]];
             eq v.r dim1, ap o_tilde [v.code; bdy; i]]
        end
      @@ fun p_tilde ->
      vin v.r v.pequiv (lam @@ fun _ -> ap o_tilde [ap v.pcode [prf]; bdy; r']) @@
      hcom v.code r r' (join [phi; boundary v.r]) p_tilde

    let coe_v ~(v : vcode) ~(r : S.t m) ~(r' : S.t m) ~(bdy : S.t m) : S.t m =
      let s_ x = ap v.r [x] in
      let pcode_ x = ap v.pcode [x] in
      let code_ x = ap v.code [x] in
      let pequiv_ x = ap v.pequiv [x] in
      let_ ~ident:(`Machine "F")
        begin
          lam ~ident:(`Machine "i") @@ fun i ->
          lam @@ fun _ ->
          Equiv.equiv_fwd @@ ap (pequiv_ i) [prf]
        end
      @@ fun f_tilde ->
      let_ ~ident:(`Machine "O")
        begin
          coe (lam code_) r r' @@ vproj (s_ r) (pcode_ r) (code_ r) (pequiv_ r) bdy
        end
      @@ fun o_tilde ->
      let_ ~ident:(`Machine "Fiber'")
        begin
          lam @@ fun _ ->
          Equiv.code_fiber (ap (pcode_ r') [prf]) (code_ r') (ap f_tilde [r'; prf]) o_tilde
        end
      @@ fun fibercode ->
      let_ ~ident:(`Machine "R")
        begin
          let line = lam ~ident:(`Machine "i") @@ fun i ->
            code_path' (lam @@ fun _ -> code_ i)
              (ap f_tilde [i; prf; coe (lam @@ fun j -> ap (pcode_ j) [prf]) r i bdy])
              (coe (lam code_) r i (ap f_tilde [r; prf; bdy]))
          in
          lam @@ fun _ ->
          coe line r r' @@ el_in @@ lam @@ fun _ -> sub_in @@ ap f_tilde [r; prf; bdy]
        end
      @@ fun r_tilde ->
      let_ ~ident:(`Machine "S")
        begin
          lam @@ fun _ ->
          Equiv.equiv_inv_path (ap (pequiv_ r') [prf]) o_tilde @@ (* "q_tilde" *)
          el_in @@ cof_split
            [forall (fun i -> eq (s_ i) dim0), pair
               (coe (lam @@ fun j -> ap (pcode_ j) [prf]) r r' bdy)
               (ap r_tilde [prf]);
             eq r r', pair bdy
               (el_in @@ lam @@ fun _ -> sub_in @@ vproj (s_ r) (pcode_ r) (code_ r) (pequiv_ r) bdy)]
        end
      @@ fun s_tilde ->
      let_ ~ident:(`Machine "T")
        begin
          lam @@ fun _ ->
          hcom (ap fibercode [prf]) dim0 dim1 (join [forall (fun i -> eq (s_ i) dim0); eq r r']) @@
          lam ~ident:(`Machine "j") @@ fun j ->
          lam @@ fun _ ->
          cof_split
            [eq j dim0, Equiv.equiv_inv (ap (pequiv_ r') [prf]) o_tilde; (* "p_tilde" *)
             join [forall (fun i -> eq (s_ i) dim0); eq r r'], sub_out @@ ap (el_out @@ ap s_tilde [prf]) [j]]
        end
      @@ fun t_tilde ->
      let_ ~ident:(`Machine "U")
        begin
          hcom (code_ r') dim1 (s_ r') (join [eq r r'; eq (s_ r') dim0]) @@
          lam ~ident:(`Machine "k") @@ fun k ->
          lam @@ fun _ ->
          cof_split
            [join [eq k dim1; eq r r'], o_tilde;
             eq (s_ r') dim0, sub_out @@ ap (el_out @@ snd @@ el_out @@ ap t_tilde [prf]) [k]]
        end
      @@ fun u_tilde ->
      vin (s_ r') (pequiv_ r') (lam @@ fun _ -> fst @@ el_out @@ ap t_tilde [prf]) u_tilde
  end

  module FHCom :
  sig
    type fhcom_u = {r : S.t m; r' : S.t m; phi : S.t m; bdy : S.t m}
    val hcom_fhcom : fhcom:fhcom_u -> r:S.t m -> r':S.t m -> phi:S.t m -> bdy:S.t m -> S.t m
    val coe_fhcom : fhcom:fhcom_u -> r:S.t m -> r':S.t m -> bdy:S.t m -> S.t m
  end =
  struct
    type fhcom_u = {r : S.t m; r' : S.t m; phi : S.t m; bdy : S.t m}

    let hcom_fhcom ~(fhcom : fhcom_u) ~(r : S.t m) ~(r' : S.t m) ~(phi : S.t m) ~(bdy : S.t m) : S.t m =
      let_ ~ident:(`Machine "O")
        begin
          lam ~ident:(`Machine "i") @@ fun i ->
          lam @@ fun _ ->
          cap fhcom.r fhcom.r' fhcom.phi fhcom.bdy @@ ap bdy [i; prf]
        end
      @@ fun o_tilde ->
      let_ ~ident:(`Machine "P")
        begin
          lam ~ident:(`Machine "i") @@ fun i ->
          lam @@ fun _ ->
          hcom (ap fhcom.bdy [fhcom.r'; prf]) r i phi bdy
        end
      @@ fun p_tilde ->
      box fhcom.r fhcom.r' fhcom.phi (lam @@ fun _ -> ap p_tilde [r'; prf]) @@
      hcom (ap fhcom.bdy [fhcom.r; prf]) r r' (join [phi; fhcom.phi; eq fhcom.r fhcom.r']) @@
      lam ~ident:(`Machine "i") @@ fun i ->
      lam @@ fun _ ->
      cof_split
        [join [eq i r; phi], ap o_tilde [i; prf];
         fhcom.phi, coe (lam ~ident:(`Machine "j") @@ fun j -> ap fhcom.bdy [j; prf]) fhcom.r' fhcom.r (ap p_tilde [i; prf]);
         eq fhcom.r fhcom.r', ap p_tilde [i; prf]]

    (* [fhcom] below is an fhcom of binders; so you need to write [ap fhcom.r [r]] etc. *)
    let coe_fhcom ~(fhcom : fhcom_u) ~(r : S.t m) ~(r' : S.t m) ~(bdy : S.t m) : S.t m =
      let s_ x = ap fhcom.r [x] in
      let s'_ x = ap fhcom.r' [x] in
      let phi_ x = ap fhcom.phi [x] in
      let code_ x = ap fhcom.bdy [x] in
      let_ ~ident:(`Machine "N")
        begin
          lam ~ident:(`Machine "i") @@ fun i ->
          lam ~ident:(`Machine "j") @@ fun j ->
          lam @@ fun _ ->
          coe (lam ~ident:(`Machine "k") @@ fun k -> ap (code_ i) [k; prf]) (s'_ i) j @@
          coe (lam ~ident:(`Machine "k") @@ fun k -> ap (code_ k) [s'_ k; prf]) r i bdy
        end
      @@ fun n_tilde ->
      let_ ~ident:(`Machine "O")
        begin
          lam ~ident:(`Machine "j") @@ fun j ->
          hcom (ap (code_ r) [s_ r; prf]) (s'_ r) j (phi_ r) @@
          lam ~ident:(`Machine "k") @@ fun k ->
          lam @@ fun _ ->
          cof_split
            [eq k (s'_ r), cap (s_ r) (s'_ r) (phi_ r) (code_ r) bdy;
             phi_ r,
             coe (lam ~ident:(`Machine "l") @@ fun l -> ap (code_ r) [l; prf]) k (s_ r) @@
             coe (lam ~ident:(`Machine "l") @@ fun l -> ap (code_ r) [l; prf]) (s'_ r) k bdy]
        end
      @@ fun o_tilde ->
      let_ ~ident:(`Machine "P")
        begin
          let line = lam ~ident:(`Machine "k") @@ fun k -> ap (code_ k) [s_ k; prf] in
          let cof = join [forall phi_; forall (fun i -> eq (s_ i) (s'_ i))] in
          com line r r' cof @@
          lam ~ident:(`Machine "i") @@ fun i ->
          lam @@ fun _ ->
          cof_split
            [eq i r, ap o_tilde [s_ r];
             forall phi_, ap n_tilde [i; s_ i; prf];
             forall (fun i -> eq (s_ i) (s'_ i)), coe (lam ~ident:(`Machine "k") @@ fun k -> ap (code_ k) [s_ k; prf]) r i bdy]
        end
      @@ fun p_tilde ->
      let_ ~ident:(`Machine "Q")
        begin
          lam ~ident:(`Machine "j") @@ fun j ->
          lam @@ fun _ ->
          let line = lam ~ident:(`Machine "k") @@ fun k -> ap (code_ r') [k; prf] in
          com line (s_ r') j (join [eq r r'; forall phi_]) @@
          lam ~ident:(`Machine "k") @@ fun k ->
          lam @@ fun _ ->
          cof_split
            [eq k (s_ r'), p_tilde;
             eq r r', coe (lam ~ident:(`Machine "l") @@ fun l -> ap (code_ r') [l; prf]) (s'_ r') k bdy;
             forall phi_, ap n_tilde [r'; k; prf]]
        end
      @@ fun q_tilde ->
      box (s_ r') (s'_ r') (phi_ r')
        (lam @@ fun _ -> ap q_tilde [s'_ r'; prf])
        begin
          hcom (code_ r') (s_ r') (s'_ r') (join [phi_ r'; eq r r']) @@
          lam @@ fun j ->
          lam @@ fun _ ->
          cof_split
            [eq j (s_ r'), p_tilde;
             phi_ r', coe (lam ~ident:(`Machine "l") @@ fun l -> ap (code_ r') [l; prf]) j (s_ r') (ap q_tilde [j; prf]);
             eq r r', ap o_tilde [j]]
        end
  end
end

module Test =
struct
  let closed_form_hcom_v =
    lam ~ident:(`Machine "s") @@ fun v_r ->
    lam ~ident:(`Machine "A") @@ fun v_pcode ->
    lam ~ident:(`Machine "B") @@ fun v_code ->
    lam ~ident:(`Machine "E") @@ fun v_pequiv ->
    lam ~ident:(`Machine "r") @@ fun r ->
    lam ~ident:(`Machine "r'") @@ fun r' ->
    lam ~ident:(`Machine "φ") @@ fun phi ->
    lam ~ident:(`Machine "M") @@ fun bdy ->
    Kan.V.hcom_v ~v:{r = v_r; pcode = v_pcode; code = v_code; pequiv = v_pequiv} ~r ~r' ~phi ~bdy

  let closed_form_coe_v =
    lam ~ident:(`Machine "s") @@ fun v_r ->
    lam ~ident:(`Machine "A") @@ fun v_pcode ->
    lam ~ident:(`Machine "B") @@ fun v_code ->
    lam ~ident:(`Machine "E") @@ fun v_pequiv ->
    lam ~ident:(`Machine "r") @@ fun r ->
    lam ~ident:(`Machine "r'") @@ fun r' ->
    lam ~ident:(`Machine "M") @@ fun bdy ->
    Kan.V.coe_v ~v:{r = v_r; pcode = v_pcode; code = v_code; pequiv = v_pequiv} ~r ~r' ~bdy

  let closed_form_hcom_fhcom =
    lam ~ident:(`Machine "s") @@ fun h_r ->
    lam ~ident:(`Machine "s'") @@ fun h_r' ->
    lam ~ident:(`Machine "ψ") @@ fun h_phi ->
    lam ~ident:(`Machine "A") @@ fun h_bdy ->
    lam ~ident:(`Machine "r") @@ fun r ->
    lam ~ident:(`Machine "r'") @@ fun r' ->
    lam ~ident:(`Machine "φ") @@ fun phi ->
    lam ~ident:(`Machine "M") @@ fun bdy ->
    Kan.FHCom.hcom_fhcom ~fhcom:{r = h_r; r' = h_r'; phi = h_phi; bdy = h_bdy} ~r ~r' ~phi ~bdy

  let closed_form_coe_fhcom =
    lam ~ident:(`Machine "s") @@ fun h_r ->
    lam ~ident:(`Machine "s'") @@ fun h_r' ->
    lam ~ident:(`Machine "φ") @@ fun h_phi ->
    lam ~ident:(`Machine "A") @@ fun h_bdy ->
    lam ~ident:(`Machine "r") @@ fun r ->
    lam ~ident:(`Machine "r'") @@ fun r' ->
    lam ~ident:(`Machine "M") @@ fun bdy ->
    Kan.FHCom.coe_fhcom ~fhcom:{r = h_r; r' = h_r'; phi = h_phi; bdy = h_bdy} ~r ~r' ~bdy

  let print_example () =
    test closed_form_hcom_v;
    test closed_form_coe_v;
    test closed_form_hcom_fhcom;
    test closed_form_coe_fhcom
end
