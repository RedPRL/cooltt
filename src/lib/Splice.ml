open CoolBasis.Bwd
open BwdNotation

module S = Syntax
module D = Domain
module TB = TermBuilder

type 'a t = D.env -> 'a TB.m * D.env

let foreign con k : _ t =
  fun env ->
  let env' = {env with conenv = env.conenv <>< [con]} in
  let var = TB.lvl @@ Bwd.length env.conenv in
  k var env'

let foreign_cof phi = foreign @@ D.cof_to_con phi
let foreign_dim r = foreign @@ D.dim_to_con r
let foreign_clo clo = foreign @@ D.Lam clo

let foreign_tp tp k : _ t =
  fun env ->
  let env' = {env with tpenv = env.tpenv <>< [tp]} in
  let var = TB.tplvl @@ Bwd.length env.tpenv in
  k var env'

let compile (t : 'a t) : D.env *'a  =
  let m, env = t {tpenv = Emp; conenv = Emp} in
  let tplen = Bwd.length env.tpenv in
  let conlen = Bwd.length env.conenv in
  env, TB.run ~tplen ~conlen m

let term (m : 'a TB.m) : 'a t =
  fun env ->
  m, env
