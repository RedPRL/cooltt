type ident = string

type binder = B of {name : ident; body : t}
and bindern = BN of {names : ident list; body : t}
and cell = Cell of {name : ident; tp : t}

and spine = Term of t

and t =
  | Var of ident
  | Let of t * binder
  | Ann of {term : t; tp : t}
  | Nat
  | Suc of t
  | Lit of int
  | Pi of cell list * t
  | Lam of bindern
  | Ap of t * spine list
  | Sg of cell list * t
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

and case = pat * t
and pat = Pat of {lbl : ident; args : pat_arg list}
and pat_arg = [`Simple of ident option | `Inductive of ident option * ident option]


type decl =
  | Def of {name : ident; def : t; tp : t}
  | NormalizeTerm of t
  | Quit

type signature = decl list

val show : t -> string

val pp_ident : Format.formatter -> ident -> unit

val pp : Format.formatter -> t -> unit