open CoolBasis.Bwd
open BwdNotation

module S = Syntax
module D = Domain
module TB = TermBuilder

type 'a t = D.env -> 'a TB.m * D.env


let compile (t : 'a t) : D.env *'a  =
  let m, env = t {tpenv = Emp; conenv = Emp} in
  let tplen = Bwd.length env.tpenv in
  let conlen = Bwd.length env.conenv in
  env, TB.run ~tplen ~conlen m

let term (m : 'a TB.m) : 'a t =
  fun env ->
  m, env

let foreign con k : _ t =
  fun env ->
  let env' = {env with conenv = env.conenv <>< [con]} in
  let var = TB.lvl @@ Bwd.length env.conenv in
  k var env'

let foreign_cof phi = foreign @@ D.cof_to_con phi
let foreign_dim r = foreign @@ D.dim_to_con r
let foreign_clo clo = foreign @@ D.Lam (`Anon, clo)

let foreign_frm frm (k : S.t TB.m -> 'a t) : 'a t =
  match frm with
  | D.KAp (_, arg) ->
    foreign arg @@ fun arg ->
    k @@ TB.lam @@ fun f -> TB.ap f [arg]
  | D.KFst ->
    k @@ TB.lam TB.fst
  | D.KSnd ->
    k @@ TB.lam TB.fst
  | D.KGoalProj ->
    k @@ TB.lam TB.goal_proj
  | D.KElOut ->
    k @@ TB.lam TB.el_out
  | D.KNatElim (mot, zero, suc) ->
    foreign mot @@ fun mot ->
    foreign zero @@ fun zero ->
    foreign suc @@ fun suc ->
    k @@ TB.lam @@ fun n ->
    TB.nat_elim mot zero suc n
  | D.KCircleElim (mot, base, loop) ->
    foreign mot @@ fun mot ->
    foreign base @@ fun base ->
    foreign loop @@ fun loop ->
    k @@ TB.lam @@ fun n ->
    TB.circle_elim mot base loop n

let rec foreign_spine spine (k : S.t TB.m -> 'a t) : 'a t=
  match spine with
  | [] ->
    k @@ TB.lam @@ fun x -> x
  | frm :: spine ->
    foreign_frm frm @@ fun frm ->
    foreign_spine spine @@ fun spine ->
    k @@ TB.lam @@ fun x -> TB.ap spine [TB.ap frm [x]]


let foreign_tp tp k : _ t =
  fun env ->
  let env' = {env with tpenv = env.tpenv <>< [tp]} in
  let var = TB.tplvl @@ Bwd.length env.tpenv in
  k var env'


module Macro =
struct
  let tp_pequiv_in_v ~r ~pcode ~code =
    foreign_dim r @@ fun r ->
    foreign pcode @@ fun pcode ->
    foreign code @@ fun code ->
    term @@
    TB.pi (TB.tp_prf (TB.eq r TB.dim0)) @@ fun _ ->
    TB.el @@ TB.Equiv.code_equiv (TB.ap pcode [TB.prf]) code
end
