open CodeUnit
module D = Domain

type t

val init : Bantorra.Manager.library -> t

val get_lib : t -> Bantorra.Manager.library

val get_num_holes : t -> int
val inc_num_holes : t -> t

(* Manipulate of scopes *)
val transform_view : shadowing:bool -> _ Namespace.pattern -> t -> (t, 'error) Namespace.result
val transform_export : shadowing:bool -> _ Namespace.pattern -> t -> (t, 'error) Namespace.result
val export_view : shadowing:bool -> _ Namespace.pattern -> t -> (t, 'error) Namespace.result
val import : shadowing:bool -> _ Namespace.pattern -> CodeUnitID.t -> t -> (t, 'error) Namespace.result

val begin_section : t -> t
val end_section : shadowing:bool -> prefix:Namespace.path option -> t -> (t, 'error) Namespace.result

val add_global : shadowing:bool -> Ident.t -> D.tp -> D.con option -> t -> (Global.t * t, 'error) Namespace.result
val get_global : Global.t -> t -> D.tp * D.con option
val resolve_global : Ident.t -> t -> Global.t option
val get_global_cof_thy : t -> Cubical.CofThy.Disj.t

(** Create and add a new code unit. *)
val begin_unit : Bantorra.Manager.library -> id -> t -> t
val end_unit : parent:t -> child:t -> t

(** Add a code unit as an import. *)
val loading_status : CodeUnitID.t -> t -> [ `Loaded | `Loading | `Unloaded ]
