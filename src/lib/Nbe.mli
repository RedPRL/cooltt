module D := Domain
module S := Syntax
module St := ElabState

exception NbeFailed of string

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
val do_tp_clo : St.t -> (S.tp, D.tp) D.clo -> D.t -> D.tp
val do_tm_clo : St.t -> (S.t, D.t) D.clo -> D.t -> D.t