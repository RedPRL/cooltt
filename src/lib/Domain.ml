module S = Syntax

open CoolBasis
open Bwd 
open TLNat

type env = {locals : t bwd}

and ('n, 't, 'o) clo = Clo of {bdy : 't; env : env} | ConstClo of 'o
[@@deriving show]

and 'n tm_clo = ('n, S.t, t) clo
and 'n tp_clo = ('n, S.tp, tp) clo

and t =
  | Lam of (ze su) tm_clo
  | Ne of {tp : tp; ne : ne}
  | Zero
  | Suc of t
  | Pair of t * t
  | Refl of t
[@@deriving show]

and tp =
  | Nat
  | Id of tp * t * t
  | Pi of tp * (ze su) tp_clo
  | Sg of tp * (ze su) tp_clo
[@@deriving show]

and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Global of Symbol.t
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of ze su tp_clo * t * (ze su su) tm_clo * ne
  | J of ze su su su tp_clo * (ze su) tm_clo * tp * t * t * ne
[@@deriving show]

and nf = Nf of {tp : tp; el : t} [@@deriving show]

let mk_var tp lev = Ne {tp; ne = Var lev}