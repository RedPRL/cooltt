open Basis
open Frontend
open Lsp.Types

module CS = ConcreteSyntax

type t = { row : int; col : int }

let of_lex_pos (pos : LexingUtil.position) : t =
  { row = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol }

let of_lsp_pos (pos : Position.t) : t =
  { row = pos.line + 1; col = pos.character }

let to_lsp_pos (pos : t) : Position.t =
  Position.create ~line:(pos.row - 1) ~character:pos.col

let to_lsp_range (start : t) (stop : t) : Range.t =
  Range.create ~start:(to_lsp_pos start) ~end_:(to_lsp_pos stop)

let located (span : LexingUtil.span) : Range.t  =
  to_lsp_range (of_lex_pos span.start) (of_lex_pos span.stop)
