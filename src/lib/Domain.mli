include module type of DomainData

open CoolBasis

val dim_to_con : dim -> con
val cof_to_con : cof -> con
val mk_var : tp -> int -> con
val push : frm -> cut -> cut


val const_tm_clo : con -> tm_clo
val un_lam : con -> tm_clo
val compose : con -> con -> con
val apply_to : con -> tm_clo

val fst : con
val snd : con


val pp_tp : tp Pp.printer
val pp_con : con Pp.printer
val pp_cut : cut Pp.printer
val pp_hd : hd Pp.printer
