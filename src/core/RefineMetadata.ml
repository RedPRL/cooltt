open Basis
open CodeUnit

module D = Domain
module S = Syntax

type hole = Hole of { ctx : (Ident.t * S.tp) list; tp : S.tp }

type t =
  | TypeAt of LexingUtil.span * Pp.env * S.tp
  | HoleAt of LexingUtil.span * Pp.env * hole


