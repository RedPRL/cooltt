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
    M.scope @@ fun tok ->
    let+ bdy = mbdy tok in
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

end

module Coercion =
struct
  open Monad.Notation (M)
  module T = Terms

  let coe_pi ~pi_line ~r ~s ~fn ~arg : S.t M.builder = 
    let split_line = D.compose (D.Destruct D.DCodePiSplit) pi_line in 
    let base_line = D.compose D.fst split_line in
    let fam_line = D.compose D.snd split_line in
    M.foreign base_line @@ fun tbase_line ->
    M.foreign fam_line @@ fun tfam_line ->
    M.foreign (D.dim_to_con r) @@ fun tr ->
    M.foreign (D.dim_to_con s) @@ fun ts ->
    M.foreign fn @@ fun tfn ->
    M.foreign arg @@ fun targ ->
    M.term @@ 
    let fib_line = T.lam @@ fun i -> T.ap tfam_line [i; T.coe tbase_line ts i targ] in
    T.coe fib_line tr ts @@
    T.ap tfn [T.coe tbase_line ts tr targ]
end
