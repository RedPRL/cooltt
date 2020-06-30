open Basis
module CS := ConcreteSyntax
module S := Syntax
module D := Domain
module EM := ElabBasics

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

  val rule : S.tp EM.m -> tac

  (** A "virtual type" is one that is only permitted to appear as the domain of a pi type *)
  val virtual_rule : S.tp EM.m -> tac

  (** Only succeeds for non-virtual types *)
  val run : tac -> S.tp EM.m

  (** Virtual types allowed *)
  val run_virtual : tac -> S.tp EM.m

  val map : (S.tp EM.m -> S.tp EM.m) -> tac -> tac
end

module rec Chk :
sig
  include Tactic

  val rule : (D.tp -> S.t EM.m) -> tac
  val brule : (D.tp * D.cof * D.tm_clo -> S.t EM.m) -> tac
  val run : tac -> D.tp -> S.t EM.m
  val brun : tac -> D.tp * D.cof * D.tm_clo -> S.t EM.m

  val syn : Syn.tac -> tac
end
and Syn :
sig
  include Tactic
  val rule : (S.t * D.tp) EM.m -> tac
  val run : tac -> (S.t * D.tp) EM.m
  val ann : Chk.tac -> Tp.tac -> tac
end


module Var :
sig
  type tac

  val prf : D.cof -> tac
  val con : tac -> D.con
  val syn : tac -> Syn.tac
end

type var = Var.tac

val abstract : ?ident:Ident.t -> D.tp -> (var -> 'a EM.m) -> 'a EM.m
