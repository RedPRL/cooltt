open Basis

module D = Domain

(* FIXME: Anti-modular *)
type fqn = { code_unit : string; index : int }


(** Some metadata about a given code unit. *)
type t = private
  { namespace : fqn Namespace.t;
    offset : int;
  }

(** Create a code unit, using a given offset. *)
val create : int -> t

(** Add a binding to a given code unit. *)
val add_global : Ident.t -> fqn -> t -> t

(** Attempt to resolve an identifier a given code unit. *)
val resolve_global : Ident.t -> t -> fqn option
