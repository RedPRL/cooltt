open CoolBasis

module S = Syntax


module M : sig 
  include Monad.S

  val scope : (S.t m -> 'a m) -> 'a m
  val run : tplen:int -> conlen:int-> 'a m -> 'a
  val lvl : int -> S.t m
  val tplvl : int -> S.tp m
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
end


include M
open Monad.Notation (M)

type 'a b = S.t m -> 'a m

let lam mbdy : _ m = 
  scope @@ fun var ->
  let+ bdy = mbdy var in
  S.Lam bdy

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


let let_ m k : _ m = 
  let+ t = m
  and+ bdy = scope k in
  S.Let (t, bdy)

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


let pi mbase mfam : _ m = 
  let+ base = mbase
  and+ fam = scope mfam in 
  S.Pi (base, fam)

let sg mbase mfam : _ m = 
  let+ base = mbase
  and+ fam = scope mfam in 
  S.Sg (base, fam)

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

let eq mr ms = 
  let+ r = mr
  and+ s = ms in 
  S.Cof (Cof.Eq (r, s))

let join mphi mpsi = 
  let+ phi = mphi
  and+ psi = mpsi in 
  S.Cof (Cof.Join (phi, psi))

let tp_dim = ret S.TpDim
let dim0 = ret S.Dim0
let dim1 = ret S.Dim0

let boundary mr = 
  join (eq mr dim0) (eq mr dim1)


module Kan =
struct
  type coe = r:S.t m -> s:S.t m -> bdy:S.t m -> S.t m
  type hcom = r:S.t m -> s:S.t m -> phi:S.t m -> bdy:S.t m -> S.t m

  let coe_pi ~base_line ~fam_line ~r ~s ~bdy : _ m = 
    lam @@ fun arg ->
    let_ (lam @@ fun i -> coe base_line s i arg) @@ fun coe_base_line ->
    let fib_line = lam @@ fun i -> ap fam_line [i; ap coe_base_line [i]] in
    coe fib_line r s @@
    ap bdy [ap coe_base_line [r]]

  let hcom_pi ~base ~fam ~r ~s ~phi ~bdy : _ m = 
    lam @@ fun arg ->
    let tfib = ap fam [arg] in
    hcom tfib r s phi @@
    lam @@ fun i ->
    lam @@ fun prf ->
    ap bdy [i; prf; arg]

  let coe_sg ~base_line ~fam_line ~r ~s ~bdy : _ m = 
    let fst_line = lam @@ fun i -> coe base_line r i @@ fst bdy in
    let fib_line = lam @@ fun i -> ap fam_line [i; ap fst_line [i]] in
    pair (ap fst_line [s]) (coe fib_line r s @@ snd bdy)

  let hcom_sg ~base ~fam ~r ~s ~phi ~bdy : _ m = 
    lam @@ fun t ->
    let p0_line = 
      lam @@ fun i ->
      hcom base r i phi @@ 
      lam @@ fun j ->
      lam @@ fun prf ->
      fst @@ ap bdy [j; prf]
    in
    let p0 = ap p0_line [s] in
    let fib_line = 
      lam @@ fun i ->
      ap fam [ap p0_line [i]]
    in
    let p1 = 
      com fib_line r s phi @@
      lam @@ fun i ->
      lam @@ fun prf ->
      snd @@ ap bdy [i; prf]
    in
    pair p0 p1

  exception Todo

  let coe_path ~fam_line ~bdry_line =
    raise Todo

  let hcom_path ~fam ~bdry = 
    raise Todo

end
