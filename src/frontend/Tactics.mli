open Core

open CodeUnit

module D := Domain
module S := Syntax
module RM := Monads.RefineM
module CS := ConcreteSyntax
module R := Refiner

open Tactic

val intro_subtypes : Chk.tac -> Chk.tac
val intro_implicit_connectives : Chk.tac -> Chk.tac
val elim_implicit_connectives : Syn.tac -> Syn.tac

val tac_nary_quantifier : ('a, 'b) R.quantifier -> (Ident.t * 'a) list -> 'b -> 'b

val match_goal : (D.tp * D.cof * D.tm_clo -> Chk.tac RM.m) -> Chk.tac

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

module Pi : sig
  val intros : (Ident.t * Chk.tac) list -> Chk.tac -> Chk.tac
end

module Tele : sig
  val of_list : (Ident.user * Chk.tac) list -> Chk.tac
end
