open CoolBasis
module CS := ConcreteSyntax
module S := Syntax
module D := Domain
module EM := ElabBasics

type chk_tac = D.tp -> S.t EM.m
type bchk_tac = D.tp * D.cof * D.tm_clo -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

module type Tactic =
sig
  type tac
  val update_span : LexingUtil.span option -> tac -> tac
end

(* general types *)
module Tp :
sig
  include Tactic

  val make : S.tp EM.m -> tac

  (** A "virtual type" is one that is only permitted to appear as the domain of a pi type *)
  val make_virtual : S.tp EM.m -> tac

  (** Only succeeds for non-virtual types *)
  val run : tac -> S.tp EM.m

  (** Virtual types allowed *)
  val run_virtual : tac -> S.tp EM.m

  val map : (S.tp EM.m -> S.tp EM.m) -> tac -> tac
end

module rec Chk :
sig
  include Tactic with type tac = chk_tac

  (** Converts a boundary-checking tactic to a checking tactic by change of base. *)
  val bchk : BChk.tac -> tac
  val syn : Syn.tac -> tac
end
and BChk :
sig
  include Tactic with type tac = bchk_tac

  (** Converts a checking tactic to a boundary-checking tactic by a chkhronous check. *)
  val chk : Chk.tac -> tac
  val syn : Syn.tac -> tac
end
and Syn :
sig
  include Tactic with type tac = syn_tac
  val ann : Chk.tac -> Tp.tac -> tac
end


module Var :
sig
  type tac

  val prf : D.cof -> tac
  val con : tac -> D.con
  val syn : tac -> syn_tac
end

type tp_tac = Tp.tac
type var = Var.tac

val abstract : D.tp -> string option -> (var -> 'a EM.m) -> 'a EM.m
