module D := Domain
module S := Syntax
module St := ElabState
module QQ := Quasiquote

exception NbeFailed of string

open Monads

val eval : S.t -> D.con evaluate
val eval_cof : S.t -> D.cof evaluate
val eval_tp : S.tp -> D.tp evaluate

val quote_con : D.tp -> D.con -> S.t quote
val quote_tp : D.tp -> S.tp quote
val quote_cut : D.cut -> S.t quote
val quote_cof : D.cof -> S.t quote

val equal_con : D.tp -> D.con -> D.con -> bool quote
val equal_tp : D.tp -> D.tp -> bool quote

val equate_con : D.tp -> D.con -> D.con -> unit quote
val equate_tp : D.tp -> D.tp -> unit quote


val do_sub_out : D.con -> D.con compute

(** A cheaper version of re-evaluation which only guarantees that the head constructor is cubically rigid *)
type 'a whnf = [`Done | `Reduce of 'a]
val whnf_con : D.con -> D.con whnf compute
val whnf_tp : D.tp -> D.tp whnf compute

val inst_tp_clo : D.tp_clo -> D.con list -> D.tp compute
val inst_tm_clo : D.tm_clo -> D.con list -> D.con compute


val quasiquote_tm : S.t QQ.builder -> D.con compute
val quasiquote_tp : S.tp QQ.builder -> D.tp compute