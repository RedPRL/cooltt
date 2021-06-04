open Basis

type dim =
  | Dim0
    (** The left endpoint of the abstract interval. *)

  | Dim1
    (** The right endpoint of the abstract interval. *)

  | DimVar of int
    (** In [cooltt], most dimension variables are represented as natural numbers (pointers into the context). *)

  | DimSym of Symbol.t
    (** Some dimension variables must be generated in a globally fresh way ({i e.g.} when computing under a binder). *)

  | DimGlobal of Symbol.t
    (** For dimensions that are defined in the signature *)

