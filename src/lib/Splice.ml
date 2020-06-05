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
      k (tm :: tms)
  in
  go cons k

let foreign_tp_list (tps : D.tp list) k : _ t =
  let rec go tps k =
    match tps with
    | [] -> k []
    | tp :: tps ->
      foreign_tp tp @@ fun tp ->
      go tps @@ fun tps ->
      k (tp :: tps)
  in
  go tps k

let compile (t : 'a t) : D.env *'a  =
  let m, env = t {tpenv = Emp; conenv = Emp} in
  let tplen = Bwd.length env.tpenv in
  let conlen = Bwd.length env.conenv in
  env, TB.run ~tplen ~conlen m

let term (m : 'a TB.m) : 'a t =
  fun env ->
  m, env

let commute_split (self : D.con) (phis : D.cof list) (action : 'a TB.m -> 'b TB.m) =
  let phis = List.map D.cof_to_con phis in
  foreign self @@ fun self ->
  foreign_list phis @@ fun phis ->
  term @@ TB.cof_split @@ List.map (fun phi -> phi, action self) phis

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

module Bdry =
struct
  let cap ~r ~r' ~phi ~code ~box =
    Cof.join [Cof.eq r r'; phi],
    foreign_dim r @@ fun r ->
    foreign_dim r' @@ fun r' ->
    foreign_cof phi @@ fun phi ->
    foreign code @@ fun code ->
    foreign box @@ fun box ->
    term @@
    TB.cof_split
      [TB.eq r r', box;
       phi, TB.coe code r' r box]

  let vproj ~r ~pcode ~code ~pequiv ~v =
    Cof.boundary r,
    foreign_dim r @@ fun r ->
    foreign pcode @@ fun _pcode ->
    foreign code @@ fun _code ->
    foreign pequiv @@ fun pequiv ->
    foreign v @@ fun v ->
    term @@
    TB.cof_split
      [TB.eq r TB.dim0, TB.ap (TB.Equiv.equiv_fwd (TB.ap pequiv [TB.prf])) [v];
       TB.eq r TB.dim1, v]

  let vin ~r ~pivot ~base =
    Cof.boundary r,
    foreign_dim r @@ fun r ->
    foreign pivot @@ fun pivot ->
    foreign base @@ fun base ->
    term @@
    TB.cof_split
      [TB.eq r TB.dim0, TB.ap pivot [TB.prf];
       TB.eq r TB.dim1, base]

  let box ~r ~r' ~phi ~sides ~cap =
    Cof.join [Cof.eq r r'; phi],
    foreign_dim r @@ fun r ->
    foreign_dim r' @@ fun r' ->
    foreign_cof phi @@ fun phi ->
    foreign cap @@ fun cap ->
    foreign sides @@ fun sides ->
    term @@
    TB.cof_split
      [TB.eq r r', cap;
       phi, TB.ap sides [TB.prf]]

  let hcom ~r ~r' ~phi ~bdy =
    Cof.join [Cof.eq r r'; phi],
    foreign_dim r' @@ fun r' ->
    foreign bdy @@ fun bdy ->
    term @@ TB.ap bdy [r'; TB.prf]

  let com = hcom

  let coe ~r ~r' ~bdy =
    Cof.eq r r',
    foreign bdy term

  let unstable_code =
    function
    | `HCom (r, s, phi, bdy) ->
      Cof.join [Cof.eq r s; phi],
      foreign_dim s @@ fun s ->
      foreign bdy @@ fun bdy ->
      term @@ TB.ap bdy [s; TB.prf]
    | `V (r, pcode, code, _) ->
      Cof.boundary r,
      foreign_dim r @@ fun r ->
      foreign pcode @@ fun pcode ->
      foreign code @@ fun code ->
      term @@
      TB.cof_split
        [TB.eq r TB.dim0, TB.ap pcode [TB.prf];
         TB.eq r TB.dim1, code]

  let unstable_frm cut ufrm =
    match ufrm with
    | D.KHCom (r, s, phi, bdy) ->
      Cof.join [Cof.eq r s; phi],
      foreign_dim s @@ fun s ->
      foreign bdy @@ fun bdy ->
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
end
