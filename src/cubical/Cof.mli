(** {1 Types } *)

(** Multiple types in [cooltt] will need to {i include} the langauge of cofibrations, relative to a particular interval algebra ['r]. Therefore, we define a family polynomial endofunctors [('r, -) cof_f] indexed in an interpretation of the interval algebra ['r].
 *)
type ('r, 'a) cof_f =
  | Eq of 'r * 'r
  | Join of 'a list
  | Meet of 'a list

(** For each interval algebra ['r], we define the {i free monad} [('r, -) cof] on the polynomial endofunctor [('r, -) cof_f]: each [('r, 'v) cof] is the language of cofibrations over an interval algebra ['r], with indeterminates drawn from ['v]. *)
type ('r, 'v) cof =
  | Cof of ('r, ('r, 'v) cof) cof_f
  | Var of 'v

(** {1 Smart constructors} *)

val var : 'v -> ('a, 'v) cof
val eq : 'a -> 'a -> ('a, 'v) cof
val join : ('a, 'v) cof list -> ('a, 'v) cof
val meet : ('a, 'v) cof list -> ('a, 'v) cof
val bot : ('a, 'v) cof
val top : ('a, 'v) cof

val boundary : Dim.dim -> (Dim.dim, 'v) cof

