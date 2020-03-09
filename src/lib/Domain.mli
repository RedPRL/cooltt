include module type of DomainData

open CoolBasis

val mk_var : tp -> int -> con
val push : frm -> cut -> cut

val pp_tp : tp Pp.printer
val pp_con : con Pp.printer