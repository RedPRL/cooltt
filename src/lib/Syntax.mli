include module type of SyntaxData

open Basis

val pp : Pp.env -> t Pp.printer
val pp_atomic : Pp.env -> t Pp.printer

val pp_tp : Pp.env -> tp Pp.printer
val pp_atomic_tp : Pp.env -> tp Pp.printer

val pp_sequent : tp Pp.printer

val dump : t Pp.printer
val dump_tp : tp Pp.printer
