type env = t list
[@@deriving show, eq]
and clos =
    Clos of {term : Syntax.t; env : env}
  | ConstClos of t
[@@deriving show, eq]
and clos2 = Clos2 of {term : Syntax.t; env : env}
[@@deriving show, eq]
and clos3 = Clos3 of {term : Syntax.t; env : env}
[@@deriving show, eq]
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sg of t * clos
  | Pair of t * t
  | Refl of t
  | Id of t * t * t
[@@deriving show, eq]
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of clos * t * clos2 * ne
  | J of clos3 * clos * t * t * t * ne
[@@deriving show, eq]
and nf =
  | Normal of {tp : t; term : t}
[@@deriving show, eq]

let mk_var tp lev = Neutral {tp; term = Var lev}
