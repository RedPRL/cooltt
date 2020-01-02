module D := Domain
module S := Syntax

exception Nbe_failed of string

(* Main functions for doing a full normalization *)
val normalize : env:S.env -> term:S.t -> tp:S.tp -> S.t

(* Functions to pass between various semantic domains *)
val eval : S.t -> D.env -> D.t
val eval_tp : S.tp -> D.env -> D.tp

val read_back_nf : int -> D.nf -> S.t
val read_back_tp : int -> D.tp -> S.tp
val read_back_ne : int -> D.ne -> S.t

val equal_nf : int -> D.nf -> D.nf -> bool
val equal_ne : int -> D.ne -> D.ne -> bool
val equal_tp : int -> D.tp -> D.tp -> bool

(* Functions to manipulate elements of the semantic domain *)
val do_tp_clo : (S.tp, D.tp) D.clo -> D.t -> D.tp
val do_tm_clo : (S.t, D.t) D.clo -> D.t -> D.t
