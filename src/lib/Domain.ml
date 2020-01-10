module S = Syntax

open CoolBasis
open Bwd 
open TLNat

type env = {locals : con bwd}


and ('n, 't, 'o) clo = 
  | Clo : {bdy : 't; env : env}  -> ('n, 't, 'o) clo
  | ElClo : ('n, S.t, con) clo -> ('n, S.tp, tp) clo
  | ConstClo : 'o -> ('n, 't, 'o) clo

and 'n tm_clo = ('n, S.t, con) clo
and 'n tp_clo = ('n, S.tp, tp) clo

and con =
  | Lam of ze su tm_clo
  | Cut of {tp : tp; cut : cut * lazy_con ref option}
  | Zero
  | Suc of con
  | Pair of con * con
  | Refl of con
  | CodeNat
  | GoalRet of con

and lazy_con = [`Do of con * frm list | `Done of con]

and cut = hd * frm list 

and tp =
  | Nat
  | Id of tp * con * con
  | Pi of tp * ze su tp_clo
  | Sg of tp * ze su tp_clo
  | Univ
  | El of cut 
  | GoalTp of string option * tp

and hd =
  | Global of Symbol.t 
  | Var of int (* De Bruijn level *)

and frm = 
  | KAp of tp * con
  | KFst 
  | KSnd
  | KNatElim of ze su tp_clo * con * ze su su tm_clo
  | KIdElim of ze su su su tp_clo * ze su tm_clo * tp * con * con
  | KGoalProj

let pp_tp fmt _ = Format.fprintf fmt "<tp>"
let pp_con fmt _ = Format.fprintf fmt "<con>"

let push frm (hd, sp) = 
  hd, sp @ [frm]

let mk_var tp lev = Cut {tp; cut = (Var lev, []), None}