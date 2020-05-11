module S = Syntax
open CoolBasis
open Bwd

type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of Symbol.t

type cof = (dim, int) Cof.cof

type env = {tpenv : tp bwd; conenv: con bwd}

and tp_clo =
  | TpClo of S.tp * env

and tm_clo =
  | Clo of S.t * env

and con =
  | Lam of tm_clo
  | Cut of {tp : tp; cut : cut}
  | Zero
  | Suc of con
  | Pair of con * con
  | GoalRet of con
  | Abort
  | SubIn of con
  | ElIn of con
  | DimCon0
  | DimCon1
  | Cof of (con, con) Cof.cof_f
  | Prf

  | CodePath of con * con
  | CodePi of con * con
  | CodeSg of con * con
  | CodeNat

  | FHCom of [`Nat] * dim * dim * cof * con

  | Destruct of dst

and tp =
  | Sub of tp * cof * tm_clo
  | Univ
  | El of con
  | UnfoldEl of cut
  | GoalTp of string option * tp
  | TpDim
  | TpCof
  | TpPrf of cof
  | Pi of tp * tp_clo
  | Sg of tp * tp_clo
  | Nat
  | TpAbort

and hd =
  | Global of Symbol.t
  | Var of int (* De Bruijn level *)
  | Coe of con * dim * dim * con
  | HCom of cut * dim * dim * cof * con
  | SubOut of cut * cof * tm_clo
  | Split of tp * cof * cof * tm_clo * tm_clo

and cut = hd * frm list

and lazy_con = [`Do of con * frm list | `Done of con]

and frm =
  | KAp of tp * con
  | KFst
  | KSnd
  | KNatElim of tp_clo * con * tm_clo
  | KGoalProj
  | KElOut

(** destructors: exotic semantic operations that don't exist in syntax; these are meant to fail on things in improper form, rather than become neutral. *)
and dst =
  | DCodePiSplit
  | DCodeSgSplit
  | DCodePathSplit
