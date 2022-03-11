open CodeUnit
module D = Domain

type t

val init : Bantorra.Manager.library -> t

val get_lib : t -> Bantorra.Manager.library

(* Manipulate of scopes *)
val push_scope : Global.t Scope.t -> t -> t
val transform_view : shadowing:bool -> _ Namespace.pattern -> t -> (t, 'error) Namespace.result
val transform_export : shadowing:bool -> _ Namespace.pattern -> t -> (t, 'error) Namespace.result
val export_view : shadowing:bool -> _ Namespace.pattern -> t -> (t, 'error) Namespace.result
val import : shadowing:bool -> Global.t Namespace.t -> t -> (t, 'error) Namespace.result
val fold : shadowing:bool -> t -> (t, 'error) Namespace.result
val resolve_global : Ident.t -> t -> Global.t option

val get_export : CodeUnitID.t -> t -> Global.t Namespace.t

val add_global : Ident.t -> D.tp -> D.con option -> t -> (Global.t * t, 'error) Namespace.result
val get_global : Global.t -> t -> D.tp * D.con option

(** Create and add a new code unit. *)
val begin_unit : Bantorra.Manager.library -> id -> t -> t
val end_unit : parent:t -> child:t -> t

(** Add a code unit as an import. *)
val loading_status : CodeUnitID.t -> t -> [ `Loaded | `Loading | `Unloaded ]
