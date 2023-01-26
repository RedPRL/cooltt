(** This is the basis of trusted inference rules for cooltt. This module also contains
    some auxiliary tactics, but these don't need to be trusted so they should be moved elsewhere. *)

module D := Domain
module S := Syntax
module RM := Monads.RefineM

open Tactic

type ('a, 'b) quantifier = 'a -> Ident.t * (var -> 'b) -> 'b

type 'a telescope =
  | Bind of Ident.user * 'a * (var -> 'a telescope)
  | Done

module Hole : sig
  val silent_hole : string option -> Chk.tac
  val unleash_hole : string option -> Chk.tac
  val silent_syn_hole : string option -> Syn.tac
  val unleash_syn_hole : string option -> Syn.tac
end

module Probe : sig
  val probe_chk : string option -> Chk.tac -> Chk.tac
  val probe_boundary : Chk.tac -> Chk.tac -> Chk.tac
  val probe_syn : string option -> Syn.tac -> Syn.tac
end

module Dim : sig
  val formation : Tp.tac
  val dim0 : Chk.tac
  val dim1 : Chk.tac
  val dim0cof : Syn.tac
  val dim1cof: Syn.tac
  val literal : int -> Chk.tac
  val literalcof : int -> Syn.tac
end

module DDim : sig
  val formation : Tp.tac
  val ddim0 : Syn.tac
  val ddim1 : Syn.tac
end

module Cof : sig
  val formation : Tp.tac
  val eq : Syn.tac -> Syn.tac -> Chk.tac
  val le : Syn.tac -> Syn.tac -> Chk.tac
  val join : Chk.tac list -> Chk.tac
  val meet : Chk.tac list -> Chk.tac
  val boundary : Syn.tac -> Chk.tac
  val dboundary : Syn.tac -> Chk.tac

  type branch_tac = {cof : Chk.tac; bdy : var -> Chk.tac}
  val split : branch_tac list -> Chk.tac
end

module Prf : sig
  val formation : Chk.tac -> Tp.tac
  val intro : Chk.tac
end

module Dom : sig
  val formation : Tp.tac
  val dim : Chk.tac
  val ddim : Chk.tac
  val cof_ty : Chk.tac
end

module Univ : sig
  val formation : Tp.tac
  val univ : Chk.tac
  val nat : Chk.tac
  val circle : Chk.tac
  val pi : Chk.tac -> Chk.tac -> Chk.tac
  val sg : Chk.tac -> Chk.tac -> Chk.tac
  val signature : [`Field of (Ident.user * Chk.tac) | `Include of Chk.tac * (Ident.user -> Ident.user option)] list -> Chk.tac
  val patch : Chk.tac -> (Ident.user -> [`Patch of Chk.tac | `Subst of Chk.tac] option) -> Chk.tac
  val total : (Ident.user * CodeUnit.Domain.con) list -> CodeUnit.Domain.con -> Chk.tac
  val partial : Chk.tac -> Chk.tac -> Chk.tac
  val sub : Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac
  val ext : int -> int -> Chk.tac  -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac
  val infer_nullary_ext : Chk.tac
  val code_v : Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac
  val coe : Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Syn.tac
  val hcom : Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Syn.tac
  val com : Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Syn.tac
end

module El : sig
  val formation : Chk.tac -> Tp.tac
  val intro : Chk.tac -> Chk.tac
  val elim : Syn.tac -> Syn.tac
end

module ElV : sig
  val intro : Chk.tac -> Chk.tac -> Chk.tac
  val elim : Syn.tac -> Syn.tac
end

module ElHCom : sig
  val intro : Chk.tac -> Chk.tac -> Chk.tac
  val elim : Syn.tac -> Syn.tac
end

module Pi : sig
  val formation : (Tp.tac, Tp.tac) quantifier
  val intro : ?ident:Ident.t -> (var -> Chk.tac) -> Chk.tac
  val apply : Syn.tac -> Chk.tac -> Syn.tac
end

module Sg : sig
  val formation : (Tp.tac, Tp.tac) quantifier
  val intro : Chk.tac -> Chk.tac -> Chk.tac

  val pi1 : Syn.tac -> Syn.tac
  val pi2 : Syn.tac -> Syn.tac
end

module Signature : sig
  val formation : Tp.tac telescope -> Tp.tac
  val intro : [`Field of Ident.user * Chk.tac |`Include of Syn.tac * (Ident.user -> Ident.user option)] list -> Chk.tac
  val proj : Syn.tac -> Ident.user -> Syn.tac

  val find_field : (Ident.user * 'a) list -> Ident.user -> 'a option
end

module Sub : sig
  val formation : Tp.tac -> Chk.tac -> (var -> Chk.tac) -> Tp.tac
  val intro : Chk.tac -> Chk.tac
  val elim : Syn.tac -> Syn.tac
end

module Nat : sig
  val formation : Tp.tac
  val literal : int -> Chk.tac
  val suc : Chk.tac -> Chk.tac
  val elim
    : Chk.tac
    -> Chk.tac
    -> Chk.tac
    -> Syn.tac
    -> Syn.tac
end

module Circle : sig
  val formation : Tp.tac
  val base : Chk.tac
  val loop : Chk.tac -> Chk.tac
  val elim
    : Chk.tac
    -> Chk.tac
    -> Chk.tac
    -> Syn.tac
    -> Syn.tac
end

module Structural : sig
  val let_ : ?ident:Ident.t -> Syn.tac -> (var -> Chk.tac) -> Chk.tac
  val let_syn : ?ident:Ident.t -> Syn.tac -> (var -> Syn.tac) -> Syn.tac
  val lookup_var : Ident.t -> Syn.tac
  val level : int -> Syn.tac
  val generalize : Ident.t -> Chk.tac -> Chk.tac
  val unfold : Ident.t list -> Chk.tac -> Chk.tac
  val abstract : name:Ident.t option -> Chk.tac -> Chk.tac
end