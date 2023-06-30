open Basis
open CodeUnit

module S := Syntax
module D := Domain
module RM := RefineMonad

module type Tactic =
sig
  type tac
  val update_span : LexingUtil.span option -> tac -> tac
  val whnf : tac -> tac
end


(* general types *)
module Tp :
sig
  include Tactic

  val rule : ?name:string -> S.tp RM.m -> tac

  (** A "virtual type" is one that is only permitted to appear as the domain of a pi type *)
  val virtual_rule : ?name:string -> S.tp RM.m -> tac

  (** Only succeeds for non-virtual types *)
  val run : tac -> S.tp RM.m

  (** Virtual types allowed *)
  val run_virtual : tac -> S.tp RM.m

  val map : (S.tp RM.m -> S.tp RM.m) -> tac -> tac
end

module rec Chk :
sig
  include Tactic

  val rule : ?name:string -> (D.tp -> S.t RM.m) -> tac
  val brule : ?name:string -> (D.tp * D.cof * D.tm_clo -> S.t RM.m) -> tac
  val run : tac -> D.tp -> S.t RM.m
  val brun : tac -> D.tp * D.cof * D.tm_clo -> S.t RM.m

  val syn : Syn.tac -> tac

  val catch : Chk.tac -> (exn -> Chk.tac) -> Chk.tac
end
and Syn :
sig
  include Tactic
  val rule : ?name:string -> (S.t * D.tp) RM.m -> tac
  val run : tac -> (S.t * D.tp) RM.m
  val ann : Chk.tac -> Tp.tac -> tac

  val catch : Syn.tac -> (exn -> Syn.tac) -> Syn.tac
end

module Tele :
sig
  include Tactic

  val rule : ?name:string -> S.tele RM.m -> tac
  val run : tac -> S.tele RM.m
end

module KanTele :
sig
  include Tactic

  val rule : ?name:string -> (D.tp -> S.kan_tele RM.m) -> tac
  val run : tac -> D.tp -> S.kan_tele RM.m
end

module Var :
sig
  type tac

  val prf : D.cof -> tac
  val con : tac -> D.con
  val syn : tac -> Syn.tac
end

type var = Var.tac

val abstract : ?ident:Ident.t -> D.tp -> (var -> 'a RM.m) -> 'a RM.m
val abstract_tele : D.tele -> (var list -> 'a RM.m) -> 'a RM.m
val abstract_kan_tele : D.kan_tele -> (var list -> 'a RM.m) -> 'a RM.m
