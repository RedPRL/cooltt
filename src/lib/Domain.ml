
type env = t list
[@@deriving show]

and ('a, 'b) clos =
    Clos of {term : 'a; env : env}
  | ConstClos of 'b
[@@deriving show]

and 'a clos2 = Clos2 of {term : 'a; env : env}
[@@deriving show]

and 'a clos3 = Clos3 of {term : 'a; env : env}
[@@deriving show]

and t =
  | Lam of (Syntax.t, t) clos
  | Neutral of {tp : tp; term : ne}
  | Zero
  | Suc of t
  | Pair of t * t
  | Refl of t
[@@deriving show]

and tp =
  | Nat
  | Id of tp * t * t
  | Pi of tp * (Syntax.tp, tp) clos
  | Sg of tp * (Syntax.tp, tp) clos
[@@deriving show]


and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of (Syntax.tp, tp) clos * t * Syntax.t clos2 * ne
  | J of Syntax.tp clos3 * (Syntax.t, t) clos * tp * t * t * ne
[@@deriving show]

and nf =
  | Nf of {tp : tp; term : t}
[@@deriving show]

let mk_var tp lev = Neutral {tp; term = Var lev}
