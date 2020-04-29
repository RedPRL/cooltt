
type ident = string [@@deriving show]

type binder = B of {name : ident; body : t}
and bindern = BN of {names : ident list; body : t}

and cell = Cell of {name : ident; tp : t}

and t =
  | Var of [`User of ident | `Level of int]
  | Let of t * binder
  | Ann of {term : t; tp : t}
  | Nat
  | Suc of t
  | Lit of int
  | Pi of cell list * t
  | Lam of bindern
  | Ap of t * t list
  | Sg of cell list * t
  | Sub of t * t * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Id of t * t * t
  | Refl
  | Univ
  | Hole of ident option
  | Underscore
  | Unfold of ident list * t
  | Elim of {mot : bindern; cases : case list; scrut : t}
  | LamElim of case list
  | Dim
  | Cof
  | CofEq of t * t
  | Join of t * t
  | Meet of t * t
  | Prf of t
  | CofSplit of (t * t) list
  | Path of t * t * t
  | Coe of t * t * t * t
[@@deriving show]

and case = pat * t
[@@deriving show]

and pat = Pat of {lbl : ident; args : pat_arg list}
[@@deriving show]

and pat_arg = [`Simple of ident option | `Inductive of ident option * ident option]
[@@deriving show]

type decl =
  | Def of {name : ident; def : t; tp : t}
  | NormalizeTerm of t
  | Quit

type signature = decl list
