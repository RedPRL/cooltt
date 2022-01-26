open Core
open Frontend
open CodeUnit

(** Common Re-Exports *)
module S = Syntax
module D = Domain

module Sem = Semantics
module TB = TermBuilder

module T = Tactic
module R = Refiner
module Elab = Elaborator
module RM = RefineMonad

(** Alcotest checker for semantic terms in some context. *)
val check_tm : (string * S.tp) list -> D.tp RM.m -> (S.t list -> D.con RM.m) Alcotest.testable
