type ident = string
type uni_level = int

type binder = Binder of {name : ident; body : t}
and binder2 = Binder2 of {name1 : ident; name2 : ident; body : t}
and binder3 = Binder3 of {name1 : ident; name2 : ident; name3 : ident; body : t}
and cell = Cell of {name : ident; ty : t}
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
  | Lam of binder
  | Ap of t * spine list
  | Sg of cell list * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Id of t * t * t
  | Refl of t
  | J of {mot : binder3; refl : binder; eq : t}
  | Box of t
  | Open of t
  | Shut of t
  | Uni of uni_level

type decl =
    Def of {name : ident; def : t; tp : t}
  | NormalizeDef of ident
  | NormalizeTerm of {term : t; tp : t}
  | Quit

type signature = decl list
