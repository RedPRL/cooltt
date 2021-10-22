open Basis
open CodeUnit

module S := Syntax
module D := Domain
module RM := RefineMonad

module type Tactic =
sig
  type tac
  val update_span : LexingUtil.span option -> tac -> tac
  val whnf : style:Semantics.whnf_style -> tac -> tac
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
end
and Syn :
sig
  include Tactic
  val rule : ?name:string -> (S.t * D.tp) RM.m -> tac
  val run : tac -> (S.t * D.tp) RM.m
  val ann : Chk.tac -> Tp.tac -> tac
end

module Var :
sig
  type tac

  val prf : D.cof -> tac
  val con : tac -> D.con
  val syn : tac -> Syn.tac
end

module TpVar :
sig
  type tac

  val tp : tac -> Tp.tac
  val abstract : ?ident:Ident.t -> (tac -> 'a RM.m) -> 'a RM.m
end

type var = Var.tac
type tp_var = TpVar.tac

val abstract : ?ident:Ident.t -> D.tp -> (var -> 'a RM.m) -> 'a RM.m
val abstract_tp : ?ident:Ident.t -> (tp_var -> 'a RM.m) -> 'a RM.m
