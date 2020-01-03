module S = Syntax

type env = {locals : t list}

and ('a, 'b) clo = Clos of {term : 'a; env : env} | ConstClos of 'b
[@@deriving show]

and 'a clo2 = Clos2 of {term : 'a; env : env} [@@deriving show]

and 'a clo3 = Clos3 of {term : 'a; env : env} [@@deriving show]

and t =
  | Lam of (S.t, t) clo
  | Neutral of {tp : tp; term : ne}
  | Zero
  | Suc of t
  | Pair of t * t
  | Refl of t
[@@deriving show]

and tp =
  | Nat
  | Id of tp * t * t
  | Pi of tp * (S.tp, tp) clo
  | Sg of tp * (S.tp, tp) clo
[@@deriving show]

and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Global of Symbol.t
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of (S.tp, tp) clo * t * S.t clo2 * ne
  | J of S.tp clo3 * (S.t, t) clo * tp * t * t * ne
[@@deriving show]

and nf = Nf of {tp : tp; term : t} [@@deriving show]

let mk_var tp lev = Neutral {tp; term = Var lev}
