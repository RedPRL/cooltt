type env = t list
and 'a clos =
    Clos of {term : 'a; env : env}
  | ConstClos of t
and 'a clos2 = Clos2 of {term : 'a; env : env}
and 'a clos3 = Clos3 of {term : 'a; env : env}
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
and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of Syntax.tp clos * t * Syntax.t clos2 * ne
  | J of Syntax.tp clos3 * Syntax.t clos * t * t * t * ne
and nf =
  | Normal of {tp : t; term : t}

val mk_var : t -> int -> t

(* val equal : t -> t -> bool
val equal_ne : ne -> ne -> bool
val equal_nf : nf -> nf -> bool *)

val pp : Format.formatter -> t -> unit
val pp_nf : Format.formatter -> nf -> unit
val pp_ne : Format.formatter -> ne -> unit

val show : t -> string
val show_nf : nf -> string
val show_ne : ne -> string
