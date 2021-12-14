open Basis
open Cubical
open Bwd

module Make (Symbol : Symbol.S) =
struct
  module S = Syntax.Make(Symbol)

  type dim = Dim.t
  type cof = (dim, int) Cof.cof

  (** A type code whose head constructor is stable under dimension substitution. *)
  type 'a stable_code =
    [ `Pi of 'a * 'a
    (** Dependent product type *)

    | `Sg of 'a * 'a
    (** Dependent sum type *)

    | `Signature of (Ident.t * 'a) list
    (** First-Class Record types *)

    | `Data of Ident.t * ctor list

    | `Ext of int * 'a * [`Global of 'a] * 'a
    (** Extension type *)

    | `Nat
    (** Natural numbers type *)

    | `Circle
    (** The circle [S1]. *)

    | `Univ
      (** A code for the universe (antinomous for now). *)
    ]

  (** A type code whose head constructor is {i not} stable under dimension substitution. *)
  and 'a unstable_code =
    [ `HCom of dim * dim * cof * 'a
    (** Formal composite types *)

    | `V of dim * 'a * 'a * 'a
      (** V types, for univalence *)
    ]

  and env = {tpenv : tp bwd; conenv: con bwd}

  (** A {i closure} combines a semantic environment with a syntactic object binding an additional variable. *)
  and 'a clo = Clo of 'a * env
  and tp_clo = S.tp clo
  and tm_clo = S.t clo
  and sign_clo = S.sign clo
  and 'e tele_clo = 'e S.telescope clo

  and 'e telescope =
    | Bind of Ident.t * con * 'e tele_clo
    | Done of 'e

  (** Value constructors are governed by {!type:con}; we do not maintain in the datatype {i a priori} any invariant that these represent whnfs (weak head normal forms). Whether a value constructor is a whnf is contingent on the ambient local state, such as the cofibration theory. *)
  and con =
    | Lam of Ident.t * tm_clo

    | BindSym of DimProbe.t * con
    (** A nominal binder of a dimension; these are used during the execution of coercion, which must probe a line of type codes with a fresh dimension. *)

    | LetSym of dim * DimProbe.t * con
    (** An explicit substitution of a dimension for a symbol. *)

    | Cut of {tp : tp; cut : cut}
    (** Our notion of {i neutral} value, a type annotated {!type:cut}. *)

    | Zero
    | Suc of con
    | Base
    | Loop of dim
    | Pair of con * con
    | Struct of (Ident.t * con) list
    | Ctor of (Ident.t * con list)
    | SubIn of con

    | ElIn of con
    (** The introduction form for the extension of a {i stable} type code only (see {!constructor:ElStable}). *)

    | Dim0
    | Dim1
    | DimProbe of DimProbe.t

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
    | Univ
    | ElCut of cut
    | ElStable of con stable_code
    | ElUnstable of con unstable_code
    | TpDim
    | TpCof
    | TpPrf of cof
    | TpSplit of (cof * tp_clo) list
    | Pi of tp * Ident.t * tp_clo
    | Sg of tp * Ident.t * tp_clo
    | Signature of sign
    | Data of datatype
    | Nat
    | Circle
    | TpLockedPrf of cof

  and sign =
    | Field of Ident.t * tp * S.sign clo
    | Empty

  (* [NOTE: Inductive Datatypes + Self Closures]
     To handle recursive occurances of an inductive datatype within a constructor,
     we close over a type variable that stands in for all recursive occurances. Then,
     when we introduce a constructor, we instantiate the closure with /the type itself/. *)
  and ctor = Ident.t * unit tele_clo

  and datatype = { self : Ident.t; ctors : ctor list }

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
    | KProj of Ident.t
    | KNatElim of con * con * con
    | KCircleElim of con * con * con

    | KElOut
    (** The elimination form for the extension of a {i stable} type code only (see {!constructor:ElStable}). *)


  (** An {i unstable} frame is a {i dimension substitution-unstable} elimination form with a hole in place of its principal argument. *)
  and unstable_frm =
    | KHCom of dim * dim * cof * con
    | KCap of dim * dim * cof * con
    | KVProj of dim * con * con * con
    | KSubOut of cof * tm_clo
    | KLockedPrfUnlock of tp * cof * con
end
