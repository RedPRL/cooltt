open Basis
open CodeUnit
module D = Domain
module S = Syntax

type t

val init : t

val get_unit : id -> t -> CodeUnit.t

val add_global : id -> Ident.t -> D.tp -> D.con option -> t -> Global.t * t

val resolve_global : id -> Ident.t -> t -> Global.t option

val get_global : Global.t -> t -> D.tp * D.con option

(** Add a code unit as an import. *)
val add_import : id -> [< `Print of string option] Yuujinchou.Pattern.t -> id -> t -> t

(** Try to get a code unit from the imports. *)
val get_import : id -> t -> CodeUnit.t option

val is_imported : id -> t -> bool

(** Create and add a new code unit. *)
val init_unit : id -> t -> t


module Metadata : sig
  type hole = Hole of { ctx : (Ident.t * S.tp) list; tp : S.tp }

  type t

  val holes : t -> (LexingUtil.span * hole) list
  val type_spans : t -> (LexingUtil.span * Pp.env * S.tp) list
end

val add_hole : LexingUtil.span -> Metadata.hole -> t -> t
val add_type_at : LexingUtil.span -> Pp.env -> S.tp -> t -> t
val get_metadata  : t -> Metadata.t
