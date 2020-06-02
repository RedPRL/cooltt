module S = Syntax
open CoolBasis
open Bwd

include Dim
type cof = (dim, int) Cof.cof

type env = {tpenv : tp bwd; conenv: con bwd}

and tp_clo =
  | TpClo of S.tp * env

and tm_clo =
  | Clo of S.t * env

and con =
  | Lam of Ident.t * tm_clo
  | BindSym of Symbol.t * con
  | LetSym of dim * Symbol.t * con
  | Cut of {tp : tp; cut : cut}
  | Zero
  | Suc of con
  | Base
  | Loop of dim
  | Pair of con * con
  | GoalRet of con
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
  | CodeCircle
  | CodeUniv
  | CodeV of dim * con * con * con

  | FHCom of [`Nat | `Circle | `Univ] * dim * dim * cof * con
  | Box of dim * dim * cof * con * con
  | VIn of dim * con * con * con

  | Split of (cof * tm_clo) list

and tp =
  | Sub of tp * cof * tm_clo
  | Univ
  | El of con
  | ElCut of cut
  | ElUnstable of [`HCom of dim * dim * cof * con | `V of dim * con * con * con]
  | GoalTp of string option * tp
  | TpDim
  | TpCof
  | TpPrf of cof
  | TpSplit of (cof * tp_clo) list
  | Pi of tp * Ident.t * tp_clo
  | Sg of tp * Ident.t * tp_clo
  | Nat
  | Circle

and hd =
  | Global of Symbol.t
  | Var of int (* De Bruijn level *)
  | Coe of con * dim * dim * con
  | HCom of cut * dim * dim * cof * con
  | Cap of dim * dim * cof * con * cut
  | VProj of dim * con * con * con * cut
  | SubOut of cut * cof * tm_clo

and cut = hd * frm list

and frm =
  | KAp of tp * con
  | KFst
  | KSnd
  | KNatElim of con * con * con
  | KCircleElim of con * con * con
  | KGoalProj
  | KElOut

let tm_abort = Split []
let tp_abort = TpSplit []
