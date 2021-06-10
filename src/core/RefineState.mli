open Basis

module D := Domain

type t

val init : string -> t
val add_global : Ident.t -> D.tp -> D.con option -> t -> CodeUnit.symbol * t
val resolve_global : Ident.t -> t -> CodeUnit.symbol option

val get_global : CodeUnit.symbol -> t -> D.tp * D.con option

(** Add a code unit as an import. *)
val add_import : string list -> CodeUnit.t -> t -> t

(** Check to see if a code unit has already been imported. *)
val has_imported : string -> t -> bool

(** Create a new code unit, and set it as the current unit. *)
val enter_unit : string -> t -> t

(** Set another code unit as our current unit. *)
val restore_unit : string -> t -> t

val get_current_unit : t -> CodeUnit.t
