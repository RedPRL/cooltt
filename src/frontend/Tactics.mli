open Core

open CodeUnit

module D := Domain
module S := Syntax
module RM := Monads.RefineM
module CS := ConcreteSyntax
module R := Refiner

open Tactic

(** Determines whether a signature is:
    `TotalAll : A total space created by the `total` tactic, where all fields but `fib` are patched
    `TotalSome : A total space created by the `total` tactic, where at least one non-`fib` field is *not* patched
    `NotTotal : Not a total space created by the `total` tactic
*)
val is_total : D.tele -> [`TotalAll | `TotalSome | `NotTotal] RM.m

val intro_subtypes_and_total : Chk.tac -> Chk.tac
val intro_implicit_connectives : Chk.tac -> Chk.tac
val elim_implicit_connectives : Syn.tac -> Syn.tac
val elim_implicit_connectives_and_total : Syn.tac -> Syn.tac
val intro_conversions : Syn.tac -> Chk.tac

(** Brings all fields of a struct into scope, potentially applying a renaming. *)
val open_ : Syn.tac -> (Ident.t -> Ident.t option) -> (var list -> Chk.tac) -> Chk.tac

(** Brings all fields of a struct into scope, potentially applying a renaming. *)
val open_syn : Syn.tac -> (Ident.t -> Ident.t option) -> (var list -> Syn.tac) -> Syn.tac

(** Attempt to extract a telescope from a signature. *)
val tele_of_sign : Tp.tac -> Tele.tac

(** Attempt to extract a kan telescope from a signature code. *)
val kan_tele_of_sign : Chk.tac -> KanTele.tac

val tac_nary_quantifier : ('a, 'b) R.quantifier -> (Ident.t * 'a) list -> 'b -> 'b

val match_goal : (D.tp * D.cof * D.tm_clo -> Chk.tac RM.m) -> Chk.tac

val refine : ((D.tp * D.cof * D.tm_clo) list -> exn option -> Chk.tac) -> Chk.tac

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
