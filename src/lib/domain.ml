type env = t list
[@@deriving show]
and 'a clos =
    Clos of {term : 'a; env : env}
  | ConstClos of t
[@@deriving show]
and 'a clos2 = Clos2 of {term : 'a; env : env}
[@@deriving show]
and 'a clos3 = Clos3 of {term : 'a; env : env}
[@@deriving show]
and t =
  | Lam of Syntax.t clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * Syntax.tp clos
  | Sg of t * Syntax.tp clos
  | Pair of t * t
  | Refl of t
  | Id of t * t * t
[@@deriving show]
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of Syntax.tp clos * t * Syntax.t clos2 * ne
  | J of Syntax.tp clos3 * Syntax.t clos * t * t * t * ne
[@@deriving show]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show]

let mk_var tp lev = Neutral {tp; term = Var lev}
