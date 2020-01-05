type ident = string

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
  | NatElim of {mot : binder; case_zero : t; case_suc : binder2; scrut : t}
  | Pi of cell list * t
  | Lam of bindern
  | Ap of t * spine list
  | Sg of cell list * t
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Id of t * t * t
  | Refl
  | IdElim of {mot : binder3; case_refl : binder; scrut : t}
  | Hole of ident option

type decl =
  | Def of {name : ident; def : t; tp : t}
  | NormalizeTerm of t
  | Quit

type signature = decl list

val show : t -> string

val pp_ident : Format.formatter -> ident -> unit

val pp : Format.formatter -> t -> unit