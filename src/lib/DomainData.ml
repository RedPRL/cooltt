module S = Syntax
open CoolBasis
open Bwd

type dim =
  | Dim0
  | Dim1
  | DimVar of int
  | DimProbe of Symbol.t

type cof = (dim, int) Cof.cof

(** Destructors: exotic semantic operations that don't exist in syntax; these
  * are meant to fail on things in improper form, rather than become neutral. *)
type dst =
  | DCodePiSplit
  | DCodeSgSplit
  | DCodePathSplit


type env = {tpenv : tp bwd; conenv: con bwd}

and tp_clo =
  | TpClo of S.tp * env

and tm_clo =
  | Clo of S.t * env

and con =
  | Lam of Ident.t * tm_clo
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
  | CodeUniv

  | FHCom of [`Nat | `Univ] * dim * dim * cof * con

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
  | Pi of tp * Ident.t * tp_clo
  | Sg of tp * Ident.t * tp_clo
  | Nat
  | TpAbort
  | TpHCom of dim * dim * cof * con

and hd =
  | Global of Symbol.t
  | Var of int (* De Bruijn level *)
  | Coe of con * dim * dim * con
  | HCom of cut * dim * dim * cof * con
  | SubOut of cut * cof * tm_clo
  | Split of tp * (cof * tm_clo) list

and cut = hd * frm list

and frm =
  | KAp of tp * con
  | KFst
  | KSnd
  | KNatElim of con * con * con
  | KGoalProj
  | KElOut
