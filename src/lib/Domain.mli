module S := Syntax
open CoolBasis
open TLNat
open Bwd

type env = [`Con of con] bwd

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
  | GoalRet of con
  | TpCode of (con, S.t) gtp

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

and cut = hd * frm list

and lazy_con = [`Do of con * frm list | `Done of con]

and frm = 
  | KAp of tp * con
  | KFst 
  | KSnd
  | KNatElim of ghost option * ze su tp_clo * con * ze su su tm_clo
  | KIdElim of ghost option * ze su su su tp_clo * ze su tm_clo * tp * con * con
  | KGoalProj

and dim =
  | Dim0
  | Dim1
  | DimVar of int (* De Bruijn level *)

and ghost = string bwd * (tp * con) list

val mk_var : tp -> int -> con
val push : frm -> cut -> cut

val pp_tp : tp Pp.printer
val pp_con : con Pp.printer