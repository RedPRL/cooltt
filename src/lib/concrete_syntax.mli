type ident = string
type uni_level = int

type binder = Binder of {name : ident; body : t}
and binder2 = Binder2 of {name1 : ident; name2 : ident; body : t}
and spine = Term of t | Tick of t
and t =
  | Var of ident
  | Let of t * binder
  | Check of {term : t; tp : t}
  | Nat
  | Suc of t
  | Lit of int
  | NRec of {mot : binder; zero : t; suc : binder2; nat : t}
  | Pi of t * binder
  | Lam of t * binder
  | Ap of t * spine list
  | Sig of t * binder
  | Pair of t * t
  | Fst of t
  | Snd of t
  | Later of binder
  | Next of binder
  | Bullet
  | Box of t
  | Open of t
  | Shut of t
  | DFix of t * binder
  | Fold of {uni : uni_level; idx_tp : t; fix_body : binder; idx : t; term : t; tick : t}
  | Unfold of {uni : uni_level; idx_tp : t; fix_body : binder; idx : t; term : t; tick : t}
  | Uni of uni_level

type decl =
    Def of {name : ident; def : t; tp : t}
  | NormalizeDef of ident
  | NormalizeTerm of {term : t; tp : t}
  | Quit

type signature = decl list
