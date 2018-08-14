type env = t list
and clos = Clos of {term : Syntax.t; env : env}
and clos2 = Clos2 of {term : Syntax.t; env : env}
and tick_clos =
    TickClos of {term : Syntax.t; env : env}
  | ConstTickClos of t
and t =
  | Lam of clos
  | Neutral of {tp : t; term : ne}
  | Nat
  | Zero
  | Suc of t
  | Pi of t * clos
  | Sig of t * clos
  | Pair of t * t
  | Later of tick_clos
  | Next of tick_clos
  | DFix of t * clos
  | Tick of int (* DeBruijn level *)
  | Bullet
  | Box of t
  | Shut of t
  | Uni of Syntax.uni_level
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | Prev of ne * int option (* None = Bullet, Some i = Tick i *)
  | Fix of t * clos * int
  | Open of ne
  | NRec of clos * nf * clos2 * ne
and nf =
  | Normal of {tp : t; term : t}
