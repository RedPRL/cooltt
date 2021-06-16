(** The purpose of this module is to transform semantic objects into syntactic objects as efficiently as possible; only user-specified top-level definitions will be unfolded, in accordance with the {i veil} (see {!val:Monads.QuM.read_veil}). *)
open Monads
open CodeUnit

module D := Domain
module S := Syntax

val quote_con : D.tp -> D.con -> S.t quote
val quote_tp : D.tp -> S.tp quote
val quote_cut : D.cut -> S.t quote
val quote_cof : D.cof -> S.t quote
val quote_dim : D.dim -> S.t quote
