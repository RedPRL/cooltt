module D := Domain
module S := Syntax
module EM := Monads.ElabM
module CS := ConcreteSyntax

open Tactic

type ('a, 'b) quantifier = 'a -> CS.ident option * 'b -> 'b


module Hole : sig
  val unleash_hole : CS.ident option -> [`Flex | `Rigid] -> bchk_tac
  val unleash_tp_hole : CS.ident option -> [`Flex | `Rigid] -> tp_tac
  val unleash_syn_hole : CS.ident option -> [`Flex | `Rigid] -> syn_tac
end

module Goal : sig
  val formation : string option -> tp_tac -> tp_tac
end

module Dim : sig 
  val formation : tp_tac
  val dim0 : chk_tac
  val dim1 : chk_tac
  val literal : int -> chk_tac
end

module Cof : sig 
  val formation : tp_tac
  val eq : chk_tac -> chk_tac -> chk_tac
end

module Prf : sig 
  val formation : chk_tac -> tp_tac
end

module Univ : sig
  val formation : tp_tac
  val nat : chk_tac
  val pi : chk_tac -> (CS.ident option * chk_tac) -> chk_tac
  val sg : chk_tac -> (CS.ident option * chk_tac) -> chk_tac
  val id : chk_tac -> chk_tac -> chk_tac -> chk_tac
  val el_formation : chk_tac -> tp_tac
end

module Pi : sig 
  val formation : (tp_tac, tp_tac) quantifier
  val intro : CS.ident option -> bchk_tac -> bchk_tac
  val apply : syn_tac -> chk_tac -> syn_tac
end

module Sg : sig
  val formation : (tp_tac, tp_tac) quantifier
  val intro : bchk_tac -> bchk_tac -> bchk_tac
  val pi1 : syn_tac -> syn_tac
  val pi2 : syn_tac -> syn_tac
end

module Sub : sig 
  val formation : tp_tac -> chk_tac -> chk_tac -> tp_tac
  val intro : bchk_tac -> bchk_tac
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

module Structural : sig
  val let_ : syn_tac -> CS.ident option * chk_tac -> chk_tac 
  val lookup_var : CS.ident -> syn_tac 
  val variable : int -> syn_tac
end

module Tactic : sig
  val tac_multi_lam : CS.ident list -> bchk_tac -> bchk_tac
  val tac_multi_apply : syn_tac -> chk_tac list -> syn_tac

  val tac_nary_quantifier : ('a, 'b) quantifier -> (CS.ident option * 'a) list -> 'b -> 'b

  val match_goal : (D.tp -> chk_tac EM.m) -> chk_tac

  module Elim : sig
    type case_tac = CS.pat * chk_tac

    val elim 
      : (CS.ident option list * tp_tac)
      -> case_tac list 
      -> syn_tac 
      -> syn_tac

    val lam_elim 
      : case_tac list 
      -> chk_tac
  end
end