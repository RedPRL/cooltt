open Basis

type t =
  | Dim0
  (** The left endpoint of the abstract interval. *)

  | Dim1
  (** The right endpoint of the abstract interval. *)

  | DimVar of int
  (** In [cooltt], most dimension variables are represented as natural numbers (pointers into the context). *)

  | DimProbe of DimProbe.t
  (** Some dimension variables must be generated to probe underneath a binder. Subject to substitution. *)

val dump : t Pp.printer
