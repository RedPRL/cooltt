open Basis

module S = Syntax

type t =
  | Hidden of S.tp
  | Return of S.tp * S.t
  | Abs of S.tp * Ident.t * t

val pp : Ident.t -> t Pp.printer
