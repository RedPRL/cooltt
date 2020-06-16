(** This is the basis of trusted inference rules for cooltt. This module also contains
    some auxiliary tactics, but these don't need to be trusted so they should be moved elsewhere. *)

module D := Domain
module S := Syntax
module EM := Monads.ElabM
module CS := ConcreteSyntax

open Tactic

type ('a, 'b) quantifier = 'a -> Ident.t * (var -> 'b) -> 'b

module Hole : sig
  val unleash_hole : string option -> [`Flex | `Rigid] -> Chk.tac
  val unleash_tp_hole : string option -> [`Flex | `Rigid] -> Tp.tac
  val unleash_syn_hole : string option -> [`Flex | `Rigid] -> Syn.tac
end

module Goal : sig
  val formation : string option -> Tp.tac -> Tp.tac
end

module Dim : sig
  val formation : Tp.tac
  val dim0 : Chk.tac
  val dim1 : Chk.tac
  val literal : int -> Chk.tac
end

module Cof : sig
  val formation : Tp.tac
  val eq : Chk.tac -> Chk.tac -> Chk.tac
  val join : Chk.tac list -> Chk.tac
  val meet : Chk.tac list -> Chk.tac
  val boundary : Chk.tac -> Chk.tac

  type branch_tac = {cof : Chk.tac; bdy : var -> Chk.tac}
  val split : branch_tac list -> Chk.tac
end

module Prf : sig
  val formation : Chk.tac -> Tp.tac
  val intro : Chk.tac
end

module Univ : sig
  val formation : Tp.tac
  val univ : Chk.tac
  val nat : Chk.tac
  val circle : Chk.tac
  val pi : Chk.tac -> Chk.tac -> Chk.tac
  val sg : Chk.tac -> Chk.tac -> Chk.tac
  val ext : int -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac
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
end

module Tactic : sig
  val intro_subtypes : Chk.tac -> Chk.tac
  val intro_implicit_connectives : Chk.tac -> Chk.tac
  val elim_implicit_connectives : Syn.tac -> Syn.tac

  val tac_nary_quantifier : ('a, 'b) quantifier -> (Ident.t * 'a) list -> 'b -> 'b

  val match_goal : (D.tp * D.cof * D.tm_clo -> Chk.tac EM.m) -> Chk.tac

  module Elim : sig
    type case_tac = CS.pat * Chk.tac

    val elim
      : Chk.tac
      -> case_tac list
      -> Syn.tac
      -> Syn.tac

    val lam_elim
      : case_tac list
      -> Chk.tac
  end
end
