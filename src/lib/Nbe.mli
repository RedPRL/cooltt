module D := Domain
module S := Syntax
module St := ElabState

exception Nbe_failed of string

(* TODO: eval functions take state?? Potential problem is reifying _old_ states in whnfs. Led to bugs in redtt. *)

(* Functions to pass between various semantic domains *)
val eval : D.env -> S.t -> St.t -> D.t
val eval_tp : D.env -> S.tp -> St.t -> D.tp

val quote_nf : St.t -> int -> D.nf -> S.t
val quote_tp : St.t -> int -> D.tp -> S.tp
val quote_ne : St.t -> int -> D.ne -> S.t

val equal_nf : St.t -> int -> D.nf -> D.nf -> bool
val equal_ne : St.t -> int -> D.ne -> D.ne -> bool
val equal_tp : St.t -> int -> D.tp -> D.tp -> bool

(* Functions to manipulate elements of the semantic domain *)
val do_tp_clo : (S.tp, D.tp) D.clo -> D.t -> St.t -> D.tp
val do_tm_clo : (S.t, D.t) D.clo -> D.t -> St.t -> D.t