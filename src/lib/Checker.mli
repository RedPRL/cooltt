(** This is a "re-typechecker" which takes core language terms and converts them into tactics.
    The invariant is that this should always succeed on well-typed core langauge terms, and
    behave like the identity function up to judgmental equality.

    This code is not actually executed at this point, but is just a proof of concept. It might
    be useful if we ever have an un-trusted module producing core language terms (which is not
    currently the case. *)

module CS := ConcreteSyntax
module S := Syntax
module EM := Monads.ElabM
module D := Domain

open Tactic

val chk_tp : S.tp -> tp_tac
val chk_tm : S.t -> chk_tac
val syn_tm : S.t -> syn_tac
