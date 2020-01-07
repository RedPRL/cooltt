module S = Syntax

open CoolBasis
open Bwd 
open TLNat

type env = {locals : con bwd}

and ('n, 't, 'o) clo = Clo of {bdy : 't; env : env} | ConstClo of 'o
[@@deriving show]

and 'n tm_clo = ('n, S.t, con) clo
and 'n tp_clo = ('n, S.tp, tp) clo

and con =
  | Lam of (ze su) tm_clo
  | Ne of {tp : tp; ne : ne}
  | Zero
  | Suc of con
  | Pair of con * con
  | Refl of con
[@@deriving show]

and tp =
  | Nat
  | Id of tp * con * con
  | Pi of tp * ze su tp_clo
  | Sg of tp * ze su tp_clo
[@@deriving show]

and hd =
  | Global of Symbol.t 
  | Var of int (* De Bruijn level *)
[@@deriving show]

and ne =
  | Hd of hd 
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NatElim of ze su tp_clo * con * ze su su tm_clo * ne
  | IdElim of ze su su su tp_clo * ze su tm_clo * tp * con * con * ne
[@@deriving show]

and nf = Nf of {tp : tp; el : con} [@@deriving show]

let mk_var tp lev = Ne {tp; ne = Hd (Var lev)}