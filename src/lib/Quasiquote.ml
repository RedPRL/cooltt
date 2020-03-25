open CoolBasis.Bwd
open BwdNotation

module S = Syntax
module D = Domain
module TB = TermBuilder

type 'a builder = D.env -> 'a TB.m * D.env
let foreign con k : _ builder =
  fun env ->
  let env' = env <>< [con] in
  let var = TB.lvl @@ Bwd.length env in
  k var env'

let compile (builder : 'a builder) : D.env *'a  = 
  let m, env = builder Emp in
  let x = TB.run ~len:(Bwd.length env) m in
  env, x

let term (m : 'a TB.m) : 'a builder = 
  fun env ->
  m, env
