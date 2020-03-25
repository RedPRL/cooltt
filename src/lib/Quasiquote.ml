open CoolBasis open CoolBasis.Bwd
open BwdNotation

module S = Syntax
module D = Domain

module M : sig 
  include Monad.S

  type 'a builder

  val foreign : D.con -> (S.t m -> 'a builder) -> 'a builder
  val compile : 'a builder -> D.env * 'a

  val term : 'a m -> 'a builder

  val scope : (S.t m -> 'a m) -> 'a m
end =
struct
  type local = {len : int}
  type token = {lvl : int}

  module M = 
  struct
    type 'a m = local -> 'a

    let ret a : _ m = 
      fun _ -> a

    let bind m f : _ m = 
      fun loc ->
      let x = m loc in
      f x loc
  end

  open Monad.Notation (M)

  type 'a builder = D.env -> 'a m * D.env

  let var tok : _ m =
    fun loc ->
    S.Var (loc.len - tok.lvl - 1)

  let foreign con k : _ builder =
    fun env ->
    let env' = env <>< [con] in
    let tok = {lvl = Bwd.length env} in
    k (var tok) env'

  let compile (builder : 'a builder) : D.env *'a  = 
    let m, env = builder Emp in
    let x = m {len = Bwd.length env} in
    env, x

  let term (m : 'a m) : 'a builder = 
    fun env ->
    m, env

  let scope (k : S.t m -> 'a m) : 'a m = 
    fun loc ->
    let tok = {lvl = loc.len} in
    k (var tok) {len = loc.len + 1}

  include M
end

module Terms = 
struct
  open Monad.Notation (M)

  let lam mbdy : _ M.m = 
    M.scope @@ fun var ->
    let+ bdy = mbdy var in
    S.Lam bdy

  let rec ap m0 ms : _ M.m = 
    match ms with
    | [] -> m0
    | m1 :: ms ->
      let* x0 = m0 in
      let* x1 = m1 in
      ap (M.ret (S.Ap (x0, x1))) ms

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


  let let_ (m : S.t m) (k : S.t m -> 'a M.m) : 'a M.m = 
    let+ t = m
    and+ bdy = M.scope k in
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
end

module Kan =
struct
  open Monad.Notation (M)
  module T = Terms

  let coe_pi ~pi_line ~r ~s ~fn : S.t M.builder = 
    let split_line = D.compose (D.Destruct D.DCodePiSplit) pi_line in 
    let base_line = D.compose D.fst split_line in
    let fam_line = D.compose D.snd split_line in
    M.foreign base_line @@ fun tbase_line ->
    M.foreign fam_line @@ fun tfam_line ->
    M.foreign (D.dim_to_con r) @@ fun tr ->
    M.foreign (D.dim_to_con s) @@ fun ts ->
    M.foreign fn @@ fun tfn ->
    M.term @@ 
    T.lam @@ fun targ ->
    T.let_ (T.lam @@ fun i -> T.coe tbase_line ts i targ) @@ fun tcoe_base_line ->
    let fib_line = T.lam @@ fun i -> T.ap tfam_line [i; T.ap tcoe_base_line [i]] in
    T.coe fib_line tr ts @@
    T.ap tfn [T.ap tcoe_base_line [tr]]

  let hcom_pi ~base ~fam ~r ~s ~phi ~bdy : S.t M.builder = 
    M.foreign base @@ fun tbase ->
    M.foreign fam @@ fun tfam ->
    M.foreign (D.dim_to_con r) @@ fun tr ->
    M.foreign (D.dim_to_con s) @@ fun ts ->
    M.foreign (D.cof_to_con phi) @@ fun tphi ->
    M.foreign bdy @@ fun tbdy ->
    M.term @@
    T.lam @@ fun t ->
    let tfib = T.ap tfam [t] in
    T.hcom tfib tr ts tphi @@
    T.lam @@ fun i ->
    T.lam @@ fun prf ->
    T.ap tbdy [i; prf; t]

  let hcom_sg ~base ~fam ~r ~s ~phi ~bdy : S.t M.builder = 
    M.foreign base @@ fun tbase ->
    M.foreign fam @@ fun tfam ->
    M.foreign (D.dim_to_con r) @@ fun tr ->
    M.foreign (D.dim_to_con s) @@ fun ts ->
    M.foreign (D.cof_to_con phi) @@ fun tphi ->
    M.foreign bdy @@ fun tbdy ->
    M.term @@
    T.lam @@ fun t ->
    let tfst_line = 
      T.lam @@ fun i ->
      T.hcom tbase tr i tphi @@ 
      T.lam @@ fun j ->
      T.lam @@ fun prf ->
      T.fst @@ T.ap tbdy [j; prf]
    in
    let tfst = T.ap tfst_line [ts] in
    let tfib_line = 
      T.lam @@ fun i ->
      T.ap tfam [T.ap tfst_line [i]]
    in
    let tsnd = 
      T.com tfib_line tr ts tphi @@
      T.lam @@ fun i ->
      T.lam @@ fun prf ->
      T.snd @@ T.ap tbdy [i; prf]
    in
    T.pair tfst tsnd

  let coe_sg ~sg_line ~r ~s ~pair : S.t M.builder = 
    let split_line = D.compose (D.Destruct D.DCodeSgSplit) sg_line in 
    let base_line = D.compose D.fst split_line in
    let fam_line = D.compose D.snd split_line in
    M.foreign base_line @@ fun tbase_line ->
    M.foreign fam_line @@ fun tfam_line ->
    M.foreign (D.dim_to_con r) @@ fun tr ->
    M.foreign (D.dim_to_con s) @@ fun ts ->
    M.foreign pair @@ fun tpair ->
    M.term @@
    let fst_line = T.lam @@ fun i -> T.coe tbase_line tr i @@ T.fst tpair in
    let fib_line = T.lam @@ fun i -> T.ap tfam_line [i; T.ap fst_line [i]] in
    let snd = T.coe fib_line tr ts @@ T.snd tpair in
    T.pair (T.ap fst_line [ts]) snd
end
