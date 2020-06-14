module S = Syntax
open Basis
open Cubical
open Bwd

type dim = Dim.dim
type cof = (dim, int) Cof.cof

type 'a stable_code =
  [ `Pi of 'a * 'a
  | `Sg of 'a * 'a
  | `Ext of int * 'a * [`Global of 'a] * 'a
  | `Nat
  | `Circle
  | `Univ
  ]

type 'a unstable_code =
  [ `HCom of dim * dim * cof * 'a
  | `V of dim * 'a * 'a * 'a
  ]

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

  | FHCom of [`Nat | `Circle] * dim * dim * cof * con

  | StableCode of con stable_code
  | UnstableCode of con unstable_code

  | Box of dim * dim * cof * con * con
  | VIn of dim * con * con * con

  | Split of (cof * tm_clo) list

and tp =
  | Sub of tp * cof * tm_clo
  | Univ
  | ElCut of cut
  | ElStable of con stable_code
  | ElUnstable of con unstable_code
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
  | UnstableCut of cut * unstable_frm

and cut = hd * frm list

and frm =
  | KAp of tp * con
  | KFst
  | KSnd
  | KNatElim of con * con * con
  | KCircleElim of con * con * con
  | KGoalProj
  | KElOut

and unstable_frm =
  | KHCom of dim * dim * cof * con
  | KCap of dim * dim * cof * con
  | KVProj of dim * con * con * con
  | KSubOut of cof * tm_clo

let tm_abort = Split []
let tp_abort = TpSplit []
