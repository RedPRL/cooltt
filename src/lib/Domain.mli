module S := Syntax
open CoolBasis
open TLNat
open Bwd

type env = {locals : t bwd}

and ('n, 't, 'o) clo = Clo of {bdy : 't; env : env} | ConstClo of 'o
and 'n tm_clo = ('n, S.t, t) clo
and 'n tp_clo = ('n, S.tp, tp) clo

and t =
  | Lam of ze su tm_clo
  | Ne of {tp : tp; ne : ne}
  | Zero
  | Suc of t
  | Pair of t * t
  | Refl of t

and tp =
  | Nat
  | Id of tp * t * t
  | Pi of tp * ze su tp_clo
  | Sg of tp * ze su tp_clo

and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Global of Symbol.t
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of ze su tp_clo * t * ze su su tm_clo * ne
  | J of ze su su su tp_clo * ze su tm_clo * tp * t * t * ne

and nf = Nf of {tp : tp; el : t}

val mk_var : tp -> int -> t

val pp : Format.formatter -> t -> unit
val pp_tp : Format.formatter -> tp -> unit
val pp_nf : Format.formatter -> nf -> unit
val pp_ne : Format.formatter -> ne -> unit

val show : t -> string
val show_tp : tp -> string
val show_nf : nf -> string
val show_ne : ne -> string