type env = t list

and ('a, 'b) clos =
    Clos of {term : 'a; env : env}
  | ConstClos of 'b

and 'a clos2 = Clos2 of {term : 'a; env : env}

and 'a clos3 = Clos3 of {term : 'a; env : env}

and t =
  | Lam of (Syntax.t, t) clos
  | Neutral of {tp : tp; term : ne}
  | Zero
  | Suc of t
  | Pair of t * t
  | Refl of t

and tp =
  | Nat
  | Id of tp * t * t
  | Pi of tp * (Syntax.tp, tp) clos
  | Sg of tp * (Syntax.tp, tp) clos


and ne =
  | Var of int (* DeBruijn levels for variables *)
  | Ap of ne * nf
  | Fst of ne
  | Snd of ne
  | NRec of (Syntax.tp, tp) clos * t * Syntax.t clos2 * ne
  | J of Syntax.tp clos3 * (Syntax.t, t) clos * tp * t * t * ne

and nf =
  | Nf of {tp : tp; term : t}

val mk_var : tp -> int -> t

(* val equal : t -> t -> bool
   val equal_ne : ne -> ne -> bool
   val equal_nf : nf -> nf -> bool *)

val pp : Format.formatter -> t -> unit
val pp_tp : Format.formatter -> tp -> unit
val pp_nf : Format.formatter -> nf -> unit
val pp_ne : Format.formatter -> ne -> unit

val show : t -> string
val show_tp : tp -> string
val show_nf : nf -> string
val show_ne : ne -> string
