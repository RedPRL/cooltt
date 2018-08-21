exception Nbe_failed of string

(* Main functions for doing a full normalization *)
val normalize : env:Syntax.env -> term:Syntax.t -> tp:Syntax.t -> Syntax.t
val initial_env : Syntax.env -> Domain.env

(* Functions to pass between various semantic domains *)
val eval : Syntax.t -> Domain.env -> Domain.t
val read_back_nf : int -> Domain.nf -> Syntax.t
val read_back_tp : int -> Domain.t -> Syntax.t
val read_back_ne : int -> Domain.ne -> Syntax.t

(* Functions to manipulate elements of the semantic domain *)
val do_clos : Domain.clos -> Domain.t -> Domain.t
val do_clos2 : Domain.clos2 -> Domain.t -> Domain.t -> Domain.t
val do_tick_clos : Domain.tick_clos -> Domain.t -> Domain.t
val do_ap : Domain.t -> Domain.t -> Domain.t
val do_prev : Domain.t -> Domain.t -> Domain.t
