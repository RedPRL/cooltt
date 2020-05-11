module S := Syntax
module D := Domain
module EM := ElabBasics

type chk_tac = D.tp -> S.t EM.m
type bchk_tac = D.tp * D.cof * D.tm_clo -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

(* general types *)
module Tp :
sig
  type tac

  val make : S.tp EM.m -> tac

  (** A "virtual type" is one that is only permitted to appear as the domain of a pi type *)
  val make_virtual : S.tp EM.m -> tac

  (** Only succeeds for non-virtual types *)
  val run : tac -> S.tp EM.m

  (** Virtual types allowed *)
  val run_virtual : tac -> S.tp EM.m

  val map : (S.tp EM.m -> S.tp EM.m) -> tac -> tac
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

(** Converts a boundary-checking tactic to a checking tactic by change of base. *)
val bchk_to_chk : bchk_tac -> chk_tac

(** Converts a checking tactic to a boundary-checking tactic by a synchronous check. *)
val chk_to_bchk : chk_tac -> bchk_tac

val syn_to_chk : syn_tac -> chk_tac
val chk_to_syn : chk_tac -> tp_tac -> syn_tac
