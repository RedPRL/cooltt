open Basis.Bwd
open Cubical
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
let foreign_clo clo = foreign @@ D.Lam (`Anon, clo)

let foreign_tp tp k : _ t =
  fun env ->
  let env' = {env with tpenv = env.tpenv <>< [tp]} in
  let var = TB.tplvl @@ Bwd.length env.tpenv in
  k var env'

let foreign_list (cons : D.con list) k : _ t =
  let rec go cons k =
    match cons with
    | [] -> k []
    | con :: cons ->
      foreign con @@ fun tm ->
      go cons @@ fun tms ->
      k @@ tm :: tms
  in
  go cons k

let compile (t : 'a t) : D.env * 'a  =
  let m, env = t {tpenv = Emp; conenv = Emp} in
  let tplen = Bwd.length env.tpenv in
  let conlen = Bwd.length env.conenv in
  env, TB.run ~tplen ~conlen m

let term (m : 'a TB.m) : 'a t =
  fun env ->
  m, env

module F =
struct
  let con = foreign
  let tp = foreign_tp
  let cons = foreign_list
  let dim = foreign_dim
  let cof = foreign_cof
  let clo = foreign_clo
end

module Macro =
struct
  let commute_split (self : D.con) (phis : D.cof list) (action : 'a TB.m -> 'b TB.m) =
    let phis = List.map D.cof_to_con phis in
    F.con self @@ fun self ->
    F.cons phis @@ fun phis ->
    term @@ TB.cof_split @@ List.map (fun phi -> phi, action self) phis

  let tp_pequiv_in_v ~r ~pcode ~code =
    F.dim r @@ fun r ->
    F.con pcode @@ fun pcode ->
    F.con code @@ fun code ->
    term @@
    TB.pi (TB.tp_prf (TB.eq r TB.dim0)) @@ fun _ ->
    TB.el @@ TB.Equiv.code_equiv (TB.ap pcode [TB.prf]) code
end

module Bdry =
struct
  let cap ~r ~r' ~phi ~code ~box =
    Cof.join [Cof.eq r r'; phi],
    F.dim r @@ fun r ->
    F.dim r' @@ fun r' ->
    F.cof phi @@ fun phi ->
    foreign code @@ fun code ->
    foreign box @@ fun box ->
    term @@
    TB.cof_split
      [TB.eq r r', box;
       phi, TB.coe code r' r box]

  let vproj ~r ~pcode ~code ~pequiv ~v =
    Cof.boundary ~dim0:Dim.Dim0 ~dim1:Dim.Dim1 r,
    F.dim r @@ fun r ->
    F.con pcode @@ fun _pcode ->
    F.con code @@ fun _code ->
    F.con pequiv @@ fun pequiv ->
    F.con v @@ fun v ->
    term @@
    TB.cof_split
      [TB.eq r TB.dim0, TB.ap (TB.Equiv.equiv_fwd (TB.ap pequiv [TB.prf])) [v];
       TB.eq r TB.dim1, v]

  let vin ~r ~pivot ~base =
    Cof.boundary ~dim0:Dim.Dim0 ~dim1:Dim.Dim1 r,
    F.dim r @@ fun r ->
    F.con pivot @@ fun pivot ->
    F.con base @@ fun base ->
    term @@
    TB.cof_split
      [TB.eq r TB.dim0, TB.ap pivot [TB.prf];
       TB.eq r TB.dim1, base]

  let box ~r ~r' ~phi ~sides ~cap =
    Cof.join [Cof.eq r r'; phi],
    F.dim r @@ fun r ->
    F.dim r' @@ fun r' ->
    F.cof phi @@ fun phi ->
    F.con cap @@ fun cap ->
    F.con sides @@ fun sides ->
    term @@
    TB.cof_split
      [TB.eq r r', cap;
       phi, TB.ap sides [TB.prf]]

  let hcom ~r ~r' ~phi ~bdy =
    Cof.join [Cof.eq r r'; phi],
    F.dim r' @@ fun r' ->
    F.con bdy @@ fun bdy ->
    term @@ TB.ap bdy [r'; TB.prf]

  let com = hcom

  let coe ~r ~r' ~bdy =
    Cof.eq r r',
    F.con bdy term

  let unstable_code =
    function
    | `HCom (r, s, phi, bdy) ->
      Cof.join [Cof.eq r s; phi],
      F.dim s @@ fun s ->
      F.con bdy @@ fun bdy ->
      term @@ TB.ap bdy [s; TB.prf]
    | `V (r, pcode, code, _) ->
      Cof.boundary ~dim0:Dim.Dim0 ~dim1:Dim.Dim1 r,
      F.dim r @@ fun r ->
      F.con pcode @@ fun pcode ->
      F.con code @@ fun code ->
      term @@
      TB.cof_split
        [TB.eq r TB.dim0, TB.ap pcode [TB.prf];
         TB.eq r TB.dim1, code]

  let unstable_frm cut ufrm =
    match ufrm with
    | D.KHCom (r, s, phi, bdy) ->
      Cof.join [Cof.eq r s; phi],
      F.dim s @@ fun s ->
      F.con bdy @@ fun bdy ->
      term @@ TB.ap bdy [s; TB.prf]
    | D.KSubOut (phi, clo) ->
      phi,
      foreign_clo clo @@ fun clo ->
      term @@ TB.ap clo [TB.prf]
    | D.KVProj (r, pcode, code, pequiv) ->
      let v = D.Cut {cut; tp = D.ElUnstable (`V (r, pcode, code, pequiv))} in
      vproj ~r ~pcode ~code ~pequiv ~v
    | D.KCap (r, r', phi, code) ->
      let box = D.Cut {cut; tp = D.ElUnstable (`HCom (r, r', phi, code))} in
      cap ~r ~r' ~phi ~code ~box
    | D.KLockedPrfUnlock (_, phi, bdy) ->
      phi,
      F.con bdy @@ fun bdy ->
      term @@ TB.ap bdy [TB.prf]
end

include F
