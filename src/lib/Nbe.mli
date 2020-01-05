module D := Domain
module S := Syntax
module St := ElabState

exception NbeFailed of string

module Monadic : sig
  open NbeMonads
  val eval : S.t -> D.t evaluate
  val eval_tp : S.tp -> D.tp evaluate
  val quote : D.tp -> D.t -> S.t quote
  val quote_tp : D.tp -> S.tp quote
  val quote_ne : D.ne -> S.t quote
  val equal : D.tp -> D.t -> D.t -> bool quote
  val equal_tp : D.tp -> D.tp -> bool quote
  val equal_ne : D.ne -> D.ne -> bool quote

  val inst_tp_clo : 'n D.tp_clo -> ('n, D.t) Vec.vec -> D.tp compute
  val inst_tm_clo : 'n D.tm_clo -> ('n, D.t) Vec.vec -> D.t compute
end

(* Functions to pass between various semantic domains *)
val eval : St.t -> D.env -> S.t -> D.t
val eval_tp : St.t -> D.env -> S.tp -> D.tp

val quote_nf : St.t -> int -> D.nf -> S.t
val quote_tp : St.t -> int -> D.tp -> S.tp
val quote_ne : St.t -> int -> D.ne -> S.t

val equal_nf : St.t -> int -> D.nf -> D.nf -> bool
val equal_ne : St.t -> int -> D.ne -> D.ne -> bool
val equal_tp : St.t -> int -> D.tp -> D.tp -> bool

(* Functions to manipulate elements of the semantic domain *)
val inst_tp_clo : St.t -> 'n D.tp_clo -> ('n, D.t) Vec.vec -> D.tp
val inst_tm_clo : St.t -> 'n D.tm_clo -> ('n, D.t) Vec.vec -> D.t