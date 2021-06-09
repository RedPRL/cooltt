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

(** The cofibration corresponding to a variable [φ : 𝔽]. *)
val var : 'v -> ('a, 'v) cof

(** Given dimensions [r, r' : 𝕀], the cofibration [r=r']. *)
val eq : 'a -> 'a -> ('a, 'v) cof

(** Given a list [φ0,...,φn : 𝔽] of cofibrations, the disjunction [φ0 ∨ ... ∨ φn]. *)
val join : ('a, 'v) cof list -> ('a, 'v) cof

(** Given a list [φ0,...,φn : 𝔽] of cofibrations, the conjunction [φ0 ∧ ... ∧ φn]. *)
val meet : ('a, 'v) cof list -> ('a, 'v) cof

(** The false cofibration, equivalent to [join []]. *)
val bot : ('a, 'v) cof

(** The true cofibration, equivalent to [meet []]. *)
val top : ('a, 'v) cof

(** The boundary [∂r] of a dimension [r : 𝕀] is the disjunction [r=0 ∨ r=1] *)
val boundary : Dim.dim -> (Dim.dim, 'v) cof

