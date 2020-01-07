module S := Syntax
open CoolBasis
open TLNat
open Bwd

type env = {locals : con bwd}

and ('n, 't, 'o) clo = Clo of {bdy : 't; env : env} | ConstClo of 'o
and 'n tm_clo = ('n, S.t, con) clo
and 'n tp_clo = ('n, S.tp, tp) clo

and con =
  | Lam of ze su tm_clo
  | Ne of {tp : tp; cut : cut}
  | Glued of {tp : tp; local : cut; global : [`Cut of cut | `Con of con] Lazy.t}
  | Zero
  | Suc of con
  | Pair of con * con
  | Refl of con

and tp =
  | Nat
  | Id of tp * con * con
  | Pi of tp * ze su tp_clo
  | Sg of tp * ze su tp_clo

and hd =
  | Global of Symbol.t 
  | Var of int (* De Bruijn level *)

and cut = hd * frm list

and frm = 
  | KAp of nf
  | KFst 
  | KSnd
  | KNatElim of ze su tp_clo * con * ze su su tm_clo
  | KIdElim of ze su su su tp_clo * ze su tm_clo * tp * con * con

and nf = Nf of {tp : tp; el : con}

val mk_var : tp -> int -> con
val push : frm -> cut -> cut

val pp_con : con Pp.printer
val pp_tp : tp Pp.printer
val pp_nf : nf Pp.printer
val pp_cut : cut Pp.printer

val show_con : con -> string
val show_tp : tp -> string
val show_nf : nf -> string
val show_cut : cut -> string