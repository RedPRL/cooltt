open Basis
open Cubical
open Bwd

module Make (Symbol : Symbol.S) =
struct
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

    | Struct of (Ident.user * t) list
    | Proj of t * Ident.user

    | Ctor of Ident.user * t list

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

    | CodeExt of int * t * [`Global of t] * t
    | CodePi of t * t
    | CodeSg of t * t
    | CodeSignature of (Ident.user * t) list
    | CodeNat
    | CodeUniv
    | CodeV of t * t * t * t
    | CodeCircle

    | ESub of sub * t
    (** Explicit substition *)

    | LockedPrfIn of t
    | LockedPrfUnlock of {tp : tp; cof : t; prf : t; bdy : t}

  and tp =
    | Univ
    | El of t
    | TpVar of int
    | TpDim
    | TpCof
    | TpPrf of t
    | TpCofSplit of (t * tp) list
    | Sub of tp * t * t
    | Pi of tp * Ident.t * tp
    | Sg of tp * Ident.t * tp
    | Signature of sign
    | Data of datatype
    | Nat
    | Circle
    | TpESub of sub * tp
    | TpLockedPrf of t

  (* TODO: Replace sign with the telescope machinery *)
  and sign = (Ident.user * tp) list

  and 'e telescope =
    | Bind of Ident.t * tp * 'e telescope
    | Done of 'e

  and datatype = { self : Ident.t; ctors : (Ident.user * unit telescope) list }

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

  module Telescope =
  struct
    let rec of_bwd (xs : (Ident.t * tp) bwd) (e : 'e) : 'e telescope =
      let rec go tele =
        function
        | Emp -> tele
        | Snoc (xs, (nm, tp)) -> go (Bind (nm, tp, tele)) xs
      in go (Done e) xs
  end
end
