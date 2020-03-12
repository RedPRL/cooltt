module D := Domain
module S := Syntax
module St := ElabState

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
val equal_cut : D.cut -> D.cut -> bool quote

val equate_con : D.tp -> D.con -> D.con -> unit quote
val equate_tp : D.tp -> D.tp -> unit quote
val equate_cut : D.cut -> D.cut -> unit quote


(** A cheaper version of re-evaluation which only guarantees that the head constructor is cubically rigid *)
type 'a whnf = [`Done | `Reduce of 'a]
val whnf_con : D.con -> D.con whnf compute
val whnf_tp : D.tp -> D.tp whnf compute

val inst_tp_clo : D.tp_clo -> D.con list -> D.tp compute
val inst_tm_clo : D.tm_clo -> D.con list -> D.con compute  