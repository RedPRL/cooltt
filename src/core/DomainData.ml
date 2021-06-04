module S = Syntax
open Basis
open Cubical
open Bwd

type dim = Dim.dim
type cof = (dim, [`L of int | `G of Symbol.t]) Cof.cof

(** A type code whose head constructor is stable under dimension substitution. *)
type 'a stable_code =
  [ `Pi of ULvl.t * 'a * 'a
  (** Dependent product type *)

  | `Sg of ULvl.t * 'a * 'a
  (** Dependent sum type *)

  | `Ext of ULvl.t * int * 'a * [`Global of 'a] * 'a
  (** Extension type *)

  | `Nat of ULvl.t
  (** Natural numbers type *)

  | `Circle of ULvl.t
  (** The circle [S1]. *)

  | `Univ of ULvl.t * ULvl.t
    (** A code for the universe. *)
  ]

(** A type code whose head constructor is {i not} stable under dimension substitution. *)
type 'a unstable_code =
  [ `HCom of ULvl.t * dim * dim * cof * 'a
  (** Formal composite types *)

  | `V of ULvl.t * dim * 'a * 'a * 'a
    (** V types, for univalence *)
  ]

type env = {tpenv : tp bwd; conenv: con bwd}

(** A {i closure} combines a semantic environment with a syntactic object binding an additional variable. *)
and 'a clo = Clo of 'a * env
and tp_clo = S.tp clo
and tm_clo = S.t clo

(** Value constructors are governed by {!type:con}; we do not maintain in the datatype {i a priori} any invariant that these represent whnfs (weak head normal forms). Whether a value constructor is a whnf is contingent on the ambient local state, such as the cofibration theory. *)
and con =
  | Lam of Ident.t * tm_clo

  | BindSym of Symbol.t * con
  (** A nominal binder of a dimension; these are used during the execution of coercion, which must probe a line of type codes with a fresh dimension. *)

  | LetSym of dim * Symbol.t * con
  (** An explicit substitution of a dimension for a symbol. *)

  | Cut of {tp : tp; cut : cut}
  (** Our notion of {i neutral} value, a type annotated {!type:cut}. *)

  | Zero
  | Suc of con
  | Base
  | Loop of dim
  | Pair of con * con
  | SubIn of con

  | ElIn of con
  (** The introduction form for the extension of a {i stable} type code only (see {!constructor:ElStable}). *)

  | Dim0
  | Dim1
  | DimProbe of Symbol.t

  | LvlMagic
  | LvlTop

  | Cof of (con, con) Cof.cof_f
  (** A mixin of the language of cofibrations (as described in {!module:Cubical.Cof}), with dimensions and indeterminates in {!type:con}. *)

  | Prf

  | FHCom of [`Nat | `Circle] * dim * dim * cof * con

  | StableCode of con stable_code
  | UnstableCode of con unstable_code

  | Box of dim * dim * cof * con * con
  | VIn of dim * con * con * con

  | Split of (cof * tm_clo) list

  | LockedPrfIn of con

and tp =
  | Sub of tp * cof * tm_clo
  | Univ of ULvl.t
  | ElCut of cut
  | ElStable of con stable_code
  | ElUnstable of con unstable_code
  | TpDim
  | TpCof
  | TpPrf of cof
  | TpSplit of (cof * tp_clo) list
  | Pi of tp * Ident.t * tp_clo
  | Sg of tp * Ident.t * tp_clo
  | Nat
  | Circle
  | TpLockedPrf of cof

(** A head is a variable (e.g. {!constructor:Global}, {!constructor:Var}), or it is some kind of unstable elimination form ({!constructor:Coe}, {!constructor:UnstableCut}). The geometry of {!type:cut}, {!type:hd}, {!type:unstable_frm} enables a very direct way to re-reduce a complex cut to whnf by following the unstable nodes to the root. *)
and hd =
  | Global of Symbol.t
  (** A top-level declaration*)

  | Var of int
  (** De Bruijn level *)

  | Coe of con * dim * dim * con
  | UnstableCut of cut * unstable_frm

(** A {!type:cut} is a value that is blocked on the computation of a {!type:hd} ("head"); when the head is computed, the list of stack frames ({!type:frm}) carried by the cut will be enacted. *)
and cut = hd * frm list

(** A {i stable} frame is a {i dimension substitution-stable} elimination form with a hole in place of its principal argument. Unstable elimination forms are governed by {!type:hd} to ease the "re-reduction" of a value to whnf under a stronger cofibration theory. *)
and frm =
  | KAp of tp * con
  | KFst
  | KSnd
  | KNatElim of con * con * con
  | KCircleElim of con * con * con

  | KElOut
  (** The elimination form for the extension of a {i stable} type code only (see {!constructor:ElStable}). *)


(** An {i unstable} frame is a {i dimension substitution-unstable} elimination form with a hole in place of its principal argument. *)
and unstable_frm =
  | KHCom of dim * dim * cof * con
  | KCap of ULvl.t * dim * dim * cof * con
  | KVProj of ULvl.t * dim * con * con * con
  | KSubOut of cof * tm_clo
  | KLockedPrfUnlock of tp * cof * con
