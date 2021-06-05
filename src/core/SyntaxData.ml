open Basis
open Cubical

type t =
  | Var of int
  | Global of Symbol.t
  | Let of t * Ident.t * t
  | Ann of t * tp

  | Zero
  | Suc of t
  | NatElim of t * t * t * t

  | Base
  | Loop of t
  | CircleElim of t * t * t * t

  | Lam of Ident.t * t
  | Ap of t * t

  | Pair of t * t
  | Fst of t
  | Snd of t

  | Coe of t * t * t * t
  | HCom of t * t * t * t * t
  | Com of t * t * t * t * t

  | SubIn of t
  | SubOut of t

  | Dim0
  | Dim1
  | Cof of (t, t) Cof.cof_f
  | ForallCof of t
  | CofSplit of (t * t) list
  | Prf

  | ElIn of t
  | ElOut of t

  | Box of t * t * t * t * t
  | Cap of t * t * t * t * t

  | VIn of t * t * t * t
  | VProj of t * t * t * t * t

  | CodeExt of t * int * t * [`Global of t] * t
  | CodePi of t * t * t
  | CodeSg of t * t * t
  | CodeNat of t
  | CodeUniv of t * t
  | CodeV of t * t * t * t * t
  | CodeCircle of t

  | CodeLift of t * t * t

  | ESub of sub * t
  (** Explicit substition *)

  | LockedPrfIn of t
  | LockedPrfUnlock of {tp : tp; cof : t; prf : t; bdy : t}

  | LvlMagic
  | LvlTop
  | LvlShift of ULvl.shift * t

and tp =
  | Univ of t
  | El of t
  | TpVar of int
  | TpLvl
  | TpDim
  | TpCof
  | TpPrf of t
  | TpCofSplit of (t * tp) list
  | Sub of tp * t * t
  | Pi of tp * Ident.t * tp
  | Sg of tp * Ident.t * tp
  | Nat
  | Circle
  | TpESub of sub * tp
  | TpLockedPrf of t

(** The language of substitions from {{:https://arxiv.org/abs/1102.2405} Abel, Coquand, and Pagano}. *)
and sub =
  | SbI
  (** The identity substitution [Γ → Γ]. *)

  | SbC of sub * sub
  (** The composition of substitutions [δ ∘ γ]. *)

  | Sb1
  (** The terminal substitution [Γ → 1]. *)

  | SbE of sub * t
  (** The universal substitution into an extended context [<γ, a>]. *)

  | SbP
  (** The projection from a extended context [Γ.A → Γ]. *)
