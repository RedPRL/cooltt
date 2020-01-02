type ident = string [@@deriving show]

type binder = B of {name : ident; body : t}

and bindern = BN of {names : ident list; body : t}

and binder2 = B2 of {name1 : ident; name2 : ident; body : t}

and binder3 = B3 of {name1 : ident; name2 : ident; name3 : ident; body : t}

and cell = Cell of {name : ident; tp : t}

and spine = Term of t

and t =
  | Var of ident
  | Let of t * binder
  | Check of {term : t; tp : t}
  | Nat
  | Suc of t
  | Lit of int
  | NRec of {mot : binder; zero : t; suc : binder2; nat : t}
  | Pi of cell list * t
  | Lam of bindern
  | Ap of t * spine list
  | Sg of cell list * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Id of t * t * t
  | Refl of t option
  | J of {mot : binder3; refl : binder; eq : t}
[@@deriving show]

type decl =
  | Def of {name : ident; def : t; tp : t}
  | NormalizeDef of ident
  | NormalizeTerm of {term : t; tp : t}
  | ElaborateType of t
  | Quit

type signature = decl list
