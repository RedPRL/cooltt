module S = Syntax

open CoolBasis
open Bwd 
open TLNat

type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of Symbol.t

type cof = dim Cof.cof

type env = [`Con of con | `Dim of dim] bwd

and ('n, 't, 'o) clo = 
  | Clo : {bdy : 't; env : env}  -> ('n, 't, 'o) clo
  | ElClo : ('n, S.t, con) clo -> ('n, S.tp, tp) clo

and 'n tm_clo = ('n, S.t, con) clo
and 'n tp_clo = ('n, S.tp, tp) clo

and line_clo = 
  | LineClo of S.t * env
  | PiCoeBaseClo of line_clo
  | PiCoeFibClo of {dest : dim; base_abs : coe_abs; arg : con; clo: line_clo}
  | SgCoeBaseClo of line_clo
  | SgCoeFibClo of {src : dim; base_abs : coe_abs; fst : con; clo: line_clo}
  | SgHComFibClo of {src : dim; base : con; fam : ze su tm_clo; cof : cof; clo : pline_clo}

and pline_clo =
  | PLineClo of S.t * env
  | AppClo of con * pline_clo
  | FstClo of pline_clo
  | SndClo of pline_clo
  | ComClo of dim * coe_abs * pline_clo

and coe_shape = [`Pi | `Sg | `Cut]
and coe_abs = CoeAbs of {clo : line_clo}

and con =
  | Lam of ze su tm_clo
  | ConCoe of coe_abs * dim * dim * con
  | ConHCom of con * dim * dim * cof * pline_clo
  | Cut of {tp : tp; cut : cut; unfold : lazy_con option}
  | Zero
  | Suc of con
  | Pair of con * con
  | Refl of con
  | GoalRet of con
  | TpCode of (con, S.t) gtp

and lazy_con = [`Do of con * frm list | `Done of con]

and cut = hd * frm list 

and tp = Tp of (tp, S.tp) gtp

and (_, _) gtp =
  | Nat : ('d, 't) gtp
  | Id : 'd * con * con -> ('d, 't) gtp
  | Pi : 'd * (ze su, 't, 'd) clo -> ('d, 't) gtp
  | Sg : 'd * (ze su, 't, 'd) clo -> ('d, 't) gtp
  | Univ : (tp, S.tp) gtp
  | El : cut -> (tp, S.tp) gtp
  | GoalTp : string option * tp -> (tp, S.tp) gtp


and hd =
  | Global of Symbol.t 
  | Var of int (* De Bruijn level *)
  | Coe of coe_abs * dim * dim * con
  | HCom of cut * dim * dim * cof * pline_clo

and frm = 
  | KAp of tp * con
  | KFst 
  | KSnd
  | KNatElim of ghost option * ze su tp_clo * con * ze su su tm_clo
  | KIdElim of ghost option * ze su su su tp_clo * ze su tm_clo * tp * con * con
  | KGoalProj

and ghost = string bwd * [`Con of (tp * con) | `Dim of dim] list

let pp_tp fmt _ = 
  Format.fprintf fmt "<tp>"

let pp_con fmt _ = 
  Format.fprintf fmt "<con>"

let push frm (hd, sp) = 
  hd, sp @ [frm]

let mk_var tp lev = 
  Cut {tp; cut = Var lev, []; unfold = None}