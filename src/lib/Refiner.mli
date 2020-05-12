(** This is the basis of trusted inference rules for cooltt. This module also contains
    some auxiliary tactics, but these don't need to be trusted so they should be moved elsewhere. *)

module D := Domain
module S := Syntax
module EM := Monads.ElabM
module CS := ConcreteSyntax

open Tactic

type ('a, 'b) quantifier = 'a -> Ident.t * (var -> 'b) -> 'b

module Hole : sig
  val unleash_hole : string option -> [`Flex | `Rigid] -> bchk_tac
  val unleash_tp_hole : string option -> [`Flex | `Rigid] -> tp_tac
  val unleash_syn_hole : string option -> [`Flex | `Rigid] -> syn_tac
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
  val join : chk_tac list -> chk_tac
  val meet : chk_tac list -> chk_tac
  val boundary : chk_tac -> chk_tac

  val split : (chk_tac * (var -> bchk_tac)) list -> bchk_tac
end

module Prf : sig
  val formation : chk_tac -> tp_tac
  val intro : bchk_tac
end

module Univ : sig
  val formation : tp_tac
  val univ : chk_tac
  val nat : chk_tac
  val pi : chk_tac -> chk_tac -> chk_tac
  val sg : chk_tac -> chk_tac -> chk_tac
  val path : chk_tac -> chk_tac -> chk_tac
  val path_with_endpoints : chk_tac -> bchk_tac -> bchk_tac -> chk_tac
  val coe : chk_tac -> chk_tac -> chk_tac -> chk_tac -> syn_tac
  val hcom : chk_tac -> chk_tac -> chk_tac -> chk_tac -> chk_tac -> syn_tac
  val auto_hcom : chk_tac -> chk_tac -> chk_tac -> chk_tac -> bchk_tac
  val com : chk_tac -> chk_tac -> chk_tac -> chk_tac -> chk_tac -> syn_tac
  val topc : syn_tac
  val botc : syn_tac
end

module El : sig
  val formation : chk_tac -> tp_tac
  val intro : bchk_tac -> bchk_tac
  val elim : syn_tac -> syn_tac
end

module Pi : sig
  val formation : (tp_tac, tp_tac) quantifier
  val intro : ?ident:Ident.t -> (var -> bchk_tac) -> bchk_tac
  val apply : syn_tac -> chk_tac -> syn_tac
end

module Sg : sig
  val formation : (tp_tac, tp_tac) quantifier
  val intro : bchk_tac -> bchk_tac -> bchk_tac

  val pi1 : syn_tac -> syn_tac
  val pi2 : syn_tac -> syn_tac
end

module Sub : sig
  val formation : tp_tac -> chk_tac -> (var -> chk_tac) -> tp_tac
  val intro : bchk_tac -> bchk_tac
  val elim : syn_tac -> syn_tac
end

module Nat : sig
  val formation : tp_tac
  val literal : int -> chk_tac
  val suc : chk_tac -> chk_tac
  val elim
    : chk_tac
    -> chk_tac
    -> chk_tac
    -> syn_tac
    -> syn_tac
end

module Structural : sig
  val let_ : ?ident:Ident.t -> syn_tac -> (var -> bchk_tac) -> bchk_tac
  val let_syn : ?ident:Ident.t -> syn_tac -> (var -> syn_tac) -> syn_tac
  val lookup_var : Ident.t -> syn_tac
  val level : int -> syn_tac
end

module Tactic : sig
  val tac_multi_apply : syn_tac -> chk_tac list -> syn_tac

  val intro_implicit_connectives : bchk_tac -> bchk_tac
  val elim_implicit_connectives : syn_tac -> syn_tac

  val tac_nary_quantifier : ('a, 'b) quantifier -> (Ident.t * 'a) list -> 'b -> 'b

  val match_goal : (D.tp -> chk_tac EM.m) -> chk_tac
  val bmatch_goal : (D.tp * D.cof * D.tm_clo -> bchk_tac EM.m) -> bchk_tac

  module Elim : sig
    type case_tac = CS.pat * chk_tac

    val elim
      : chk_tac
      -> case_tac list
      -> syn_tac
      -> syn_tac

    val lam_elim
      : case_tac list
      -> bchk_tac
  end
end
