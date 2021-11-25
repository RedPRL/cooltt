open Basis
open CodeUnit

module D = Domain
module S = Syntax

type t =
  | TypeAt of LexingUtil.span * Pp.env * S.tp


