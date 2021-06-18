open CodeUnit
module D = Domain

type t

val init : string -> t
val add_global : Ident.t -> Definition.t -> t -> Global.t * t
val resolve_global : Ident.t -> t -> Global.t option

val get_global : Global.t -> t -> Definition.t
val get_global_tp : Global.t -> t -> D.tp

(** Add a code unit as an import. *)
val add_import : string list -> CodeUnit.t -> t -> t

(** Try to get a code unit from the imports. *)
val get_import : string -> t -> CodeUnit.t option

(** Create a new code unit, and set it as the current unit. *)
val enter_unit : string -> t -> t

(** Set another code unit as our current unit. *)
val restore_unit : string -> t -> t

val get_current_unit : t -> CodeUnit.t
