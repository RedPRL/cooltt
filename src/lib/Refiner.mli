module D := Domain
module S := Syntax
module EM := Monads.ElabM
module CS := ConcreteSyntax

type tp_tac = S.tp EM.m
type chk_tac = D.tp -> S.t EM.m
type syn_tac = (S.t * D.tp) EM.m

type quantifier_tac = tp_tac -> CS.ident option * tp_tac -> tp_tac


module Hole : sig
  val unleash_hole : CS.ident option -> [`Flex | `Rigid] -> chk_tac
  val unleash_tp_hole : CS.ident option -> [`Flex | `Rigid] -> tp_tac
  val unleash_syn_hole : CS.ident option -> [`Flex | `Rigid] -> syn_tac
end


module Univ : sig
  val formation : tp_tac
  val nat : chk_tac
end

module Pi : sig 
  val formation : quantifier_tac
  val intro : CS.ident option -> chk_tac -> chk_tac
  val apply : syn_tac -> chk_tac -> syn_tac
end

module Sg : sig
  val formation : quantifier_tac
  val intro : chk_tac -> chk_tac -> chk_tac
  val pi1 : syn_tac -> syn_tac
  val pi2 : syn_tac -> syn_tac
end

module Id : sig 
  val formation : tp_tac -> chk_tac -> chk_tac -> tp_tac
  val intro : chk_tac
  val elim 
    : (CS.ident option * CS.ident option * CS.ident option * tp_tac) 
    -> (CS.ident option * chk_tac) 
    -> syn_tac 
    -> syn_tac
end

module Nat : sig 
  val formation : tp_tac
  val literal : int -> chk_tac
  val suc : chk_tac -> chk_tac
  val elim 
    : (CS.ident option * tp_tac)
    -> chk_tac
    -> (CS.ident option * CS.ident option * chk_tac)
    -> syn_tac
    -> syn_tac
end

module El : sig 
  val formation : chk_tac -> tp_tac
end

module Structural : sig
  val syn_to_chk : syn_tac -> chk_tac
  val chk_to_syn : chk_tac -> tp_tac -> syn_tac
  val let_ : syn_tac -> CS.ident option * chk_tac -> chk_tac 
  val lookup_var : CS.ident -> syn_tac 
end

module Tactic : sig
  val tac_multi_lam : CS.ident list -> chk_tac -> chk_tac
  val tac_multi_apply : syn_tac -> chk_tac list -> syn_tac
  val tac_nary_quantifier : quantifier_tac -> (CS.ident option * tp_tac) list -> tp_tac -> tp_tac
end