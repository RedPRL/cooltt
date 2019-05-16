exception Nbe_failed of string

(* Main functions for doing a full normalization *)
val normalize : env:Syntax.env -> term:Syntax.t -> tp:Syntax.t -> Syntax.t

(* Functions to pass between various semantic domains *)
val eval : Syntax.t -> Domain.env -> Domain.t
val read_back_nf : int -> Domain.nf -> Syntax.t (* Note that read_back is referred to as quotation in the paper *)
val read_back_tp : int -> Domain.t -> Syntax.t
val read_back_ne : int -> Domain.ne -> Syntax.t

val check_nf : int -> Domain.nf -> Domain.nf -> bool
val check_ne : int -> Domain.ne -> Domain.ne -> bool
val check_tp : subtype:bool -> int -> Domain.t -> Domain.t -> bool

(* Functions to manipulate elements of the semantic domain *)
val do_clos : Domain.clos -> Domain.t -> Domain.t
