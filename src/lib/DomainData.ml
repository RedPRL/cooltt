module S = Syntax
open CoolBasis
open TLNat
open Bwd

type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of Symbol.t

type cof = (int, dim) Cof.cof

type env = con bwd

and ('n, 't, 'o) clo = 
  | Clo : {bdy : 't; env : env}  -> ('n, 't, 'o) clo
  | ElClo : ('n, S.t, con) clo -> ('n, S.tp, tp) clo

and 'n tm_clo = ('n, S.t, con) clo
and 'n tp_clo = ('n, S.tp, tp) clo

(** line closures *)
and _ line_clo = 
  | LineClo : 'a * env -> 'a line_clo
  | PiCoeBaseClo : S.t line_clo -> S.t line_clo
  | PiCoeFibClo : {dest : dim; base_abs : coe_abs; arg : con; clo: S.t line_clo} -> S.t line_clo
  | SgCoeBaseClo : S.t line_clo -> S.t line_clo
  | SgCoeFibClo : {src : dim; base_abs : coe_abs; fst : con; clo: S.t line_clo} -> S.t line_clo
  | SgHComFibClo : {src : dim; base : con; fam : ze su tm_clo; cof : cof; clo : S.t pline_clo} -> S.t line_clo

(** partial line closures *)
and _ pline_clo =
  | PLineClo : 'a * env -> 'a pline_clo
  | AppClo : con * S.t pline_clo -> S.t pline_clo
  | FstClo : S.t pline_clo -> S.t pline_clo
  | SndClo : S.t pline_clo -> S.t pline_clo
  | ComClo : dim * coe_abs * S.t pline_clo -> S.t pline_clo

(* partial element closures *)
and _ pclo =
  | PClo : 'a * env -> 'a pclo

and coe_abs = CoeAbs of {clo : S.t line_clo}

and con =
  | Lam of ze su tm_clo
  | ConCoe of coe_abs * dim * dim * con
  | ConHCom of con * dim * dim * cof * S.t pline_clo
  | Cut of {tp : tp; cut : cut; unfold : lazy_con option}
  | Zero
  | Suc of con
  | Pair of con * con
  | Refl of con
  | GoalRet of con
  | TpCode of (con, S.t) gtp
  | Abort
  | SubIn of S.t pclo
  | DimCon0
  | DimCon1
  | CofCon of (con, con) Cof.cof
  | Prf

and tp = Tp of (tp, S.tp) gtp

and (_, _) gtp =
  | Nat : ('d, 't) gtp
  | Id : 'd * con * con -> ('d, 't) gtp
  | Pi : 'd * (ze su, 't, 'd) clo -> ('d, 't) gtp
  | Sg : 'd * (ze su, 't, 'd) clo -> ('d, 't) gtp
  | Sub : 'd * cof * S.t pclo -> ('d, 't) gtp
  | Univ : (tp, S.tp) gtp
  | El : cut -> (tp, S.tp) gtp
  | GoalTp : string option * tp -> (tp, S.tp) gtp
  | TpDim : (tp, S.tp) gtp
  | TpPrf : cof -> (tp, S.tp) gtp

and hd =
  | Global of Symbol.t 
  | Var of int (* De Bruijn level *)
  | Coe of coe_abs * dim * dim * con
  | HCom of cut * dim * dim * cof * S.t pline_clo

and cut = hd * frm list

and lazy_con = [`Do of con * frm list | `Done of con]

and frm = 
  | KAp of tp * con
  | KFst 
  | KSnd
  | KNatElim of ghost option * ze su tp_clo * con * ze su su tm_clo
  | KIdElim of ghost option * ze su su su tp_clo * ze su tm_clo * tp * con * con
  | KGoalProj
  | KSubOut

and ghost = string bwd * (tp * con) list