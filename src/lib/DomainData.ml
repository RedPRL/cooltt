module S = Syntax
open CoolBasis
open Bwd

type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of Symbol.t

type cof = (dim, int) Cof.cof

type env = con bwd

and ('t, 'o) clo = 
  | Clo : {bdy : 't; env : env}  -> ('t, 'o) clo
  | ElClo : (S.t, con) clo -> (S.tp, tp) clo
  | PiCoeBaseClo : (S.t, con) clo -> (S.t, con) clo
  | PiCoeFibClo : {dest : dim; base_abs : coe_abs; arg : con; clo: (S.t, con) clo} -> (S.t, con) clo
  | SgCoeBaseClo : (S.t, con) clo -> (S.t, con) clo
  | SgCoeFibClo : {src : dim; base_abs : coe_abs; fst : con; clo: (S.t, con) clo} -> (S.t, con) clo
  | SgHComFibClo : {src : dim; base : con; fam : tm_clo; cof : cof; clo : (S.t, con) clo} -> (S.t, con) clo
  | AppClo : con * (S.t, con) clo -> (S.t, con) clo
  | FstClo : (S.t, con) clo -> (S.t, con) clo
  | SndClo : (S.t, con) clo -> (S.t, con) clo
  | ComClo : dim * coe_abs * (S.t, con) clo -> (S.t, con) clo
  | ConstClo : con -> (S.t, con) clo
  | ConstTpClo : tp -> (S.tp, tp) clo
  | SplitClo : tp * cof * cof * (S.t, con) clo * (S.t, con) clo -> (S.t, con) clo
  | SubOutClo : (S.t, con) clo -> (S.t, con) clo 

  | CloFromPathData : con * con -> (S.tp, tp) clo
  | CloBoundaryType : con -> (S.tp, tp) clo
  | CloFromFun : con -> (S.t, con) clo

and tm_clo = (S.t, con) clo
and tp_clo = (S.tp, tp) clo

and coe_abs = CoeAbs of {clo : tm_clo}

and con =
  | Lam of tm_clo
  | ConCoe of coe_abs * dim * dim * con
  | ConHCom of con * dim * dim * cof * (S.t, con) clo
  | Cut of {tp : tp; cut : cut; unfold : lazy_con option}
  | Zero
  | Suc of con
  | Pair of con * con
  | Refl of con
  | GoalRet of con
  | TpCode of (con, S.t) gtp
  | Abort
  | SubIn of con
  | DimCon0
  | DimCon1
  | Cof of (con, con) Cof.cof_f
  | Prf

  | CodePath of con * con


and tp = 
  | Tp of (tp, S.tp) gtp
  | Sub of tp * cof * tm_clo
  | Univ
  | El of cut
  | GoalTp of string option * tp
  | TpDim 
  | TpCof
  | TpPrf of cof 

and (_, _) gtp =
  | Nat : ('d, 't) gtp
  | Id : 'd * con * con -> ('d, 't) gtp
  | Pi : 'd * ('t, 'd) clo -> ('d, 't) gtp
  | Sg : 'd * ('t, 'd) clo -> ('d, 't) gtp

and hd =
  | Global of Symbol.t 
  | Var of int (* De Bruijn level *)
  | Coe of coe_abs * dim * dim * con
  | HCom of cut * dim * dim * cof * tm_clo
  | SubOut of cut * cof * tm_clo
  | Split of tp * cof * cof * tm_clo * tm_clo

and cut = hd * frm list

and lazy_con = [`Do of con * frm list | `Done of con]

and frm = 
  | KAp of tp * con
  | KFst 
  | KSnd
  | KNatElim of ghost option * tp_clo * con * tm_clo
  | KIdElim of ghost option * tp_clo * tm_clo * tp * con * con
  | KGoalProj

and ghost = string bwd * (tp * con) list