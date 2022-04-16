open Core

open CodeUnit

module D := Domain
module S := Syntax
module RM := Monads.RefineM
module CS := ConcreteSyntax
module R := Refiner

open Tactic

val is_total : D.sign -> [`TotalAll of D.tp | `TotalSome of D.tp | `NotTotal] RM.m
val is_total_code : (Ident.user * D.con) list -> [`TotalAll of D.tp | `TotalSome of D.tp | `NotTotal] RM.m

val intro_subtypes : Chk.tac -> Chk.tac
val intro_implicit_connectives : Chk.tac -> Chk.tac
val elim_implicit_connectives : Syn.tac -> Syn.tac
val elim_implicit_connectives_and_total : Syn.tac -> Syn.tac
val intro_conversions : Syn.tac -> Chk.tac

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

module Equations : sig
  val step : Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Chk.tac -> Syn.tac
  val qed : Chk.tac -> Chk.tac -> Syn.tac
end
