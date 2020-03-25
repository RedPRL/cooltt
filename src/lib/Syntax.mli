include module type of SyntaxData

open CoolBasis

val pp : Pp.env -> t Pp.printer
val pp_tp : Pp.env -> tp Pp.printer
val pp_sequent : names:string list -> tp Pp.printer
