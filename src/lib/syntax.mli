type uni_level = int
type t =
  | Var of int (* DeBruijn indices for variables & ticks *)
  | Nat | Zero | Suc of t | NRec of (* BINDS *) t * t * (* BINDS 2 *) t * t
  | Pi of t * (* BINDS *) t | Lam of (* BINDS *) t | Ap of t * t
  | Sig of t * (* BINDS *) t | Pair of t * t | Fst of t | Snd of t
  | Later of (* BINDS *) t | Next of (* BINDS *) t | Prev of t * t | Bullet
  | Box of t | Open of t | Shut of t
  | DFix of t * (* binds *) t
  | Uni of uni_level

type env = t list

val of_sexp : Sexplib.Sexp.t -> t
val to_sexp : Sexplib.Sexp.t list -> t -> Sexplib.Sexp.t
val pp : t -> string
