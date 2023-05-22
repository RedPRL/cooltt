(** The purpose of this module is to transform semantic objects into syntactic objects as efficiently as possible. *)
open Monads
open CodeUnit

module D := Domain
module S := Syntax

val quote_con : D.tp -> D.con -> S.t quote
val quote_tp : D.tp -> S.tp quote
val quote_tele : D.tele -> S.tele quote
val quote_kan_tele : D.kan_tele -> S.kan_tele quote
val quote_cut : D.cut -> S.t quote
val quote_cof : D.cof -> S.t quote
val quote_dim : D.dim -> S.t quote
