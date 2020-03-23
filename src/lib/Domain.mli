include module type of DomainData

open CoolBasis

val dim_to_con : dim -> con
val mk_var : tp -> int -> con
val push : frm -> cut -> cut


val const_tm_clo : con -> tm_clo
val clo_from_fun : con -> tm_clo


val pp_tp : tp Pp.printer
val pp_con : con Pp.printer
