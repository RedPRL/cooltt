open Basis
open Frontend
open Lsp.Types

module CS = ConcreteSyntax

type t = { row : int; col : int }

type range = { start : t; stop: t }

(* these functions might result into invalid positions such as
   "row 10, col 0" or "row 1, col 100" (where there are only 99
   characters at row 1), but the correctness of range lookup
   should not be (hopefully) intact. *)
let minus_one p = {p with col = p.col - 1}
let plus_one p = {p with col = p.col + 1}
let cut_range_after p r = {r with stop = minus_one p}
let cut_range_before p r = {r with start = plus_one p}

let compare p1 p2 = CCOrd.(int p1.row p2.row <?> (int, p1.col, p2.col))

let of_lex_pos (pos : LexingUtil.position) : t =
  { row = pos.pos_lnum; col = pos.pos_cnum - pos.pos_bol }

let of_lsp_pos (pos : Position.t) : t =
  { row = pos.line + 1; col = pos.character }

let of_lex_span (span : LexingUtil.span) : range =
  { start = of_lex_pos span.start; stop = of_lex_pos span.stop }

let of_lsp_range (range : Range.t) : range =
  { start = of_lsp_pos (range.start); stop = of_lsp_pos range.end_ }

let to_lsp_pos (pos : t) : Position.t =
  Position.create ~line:(pos.row - 1) ~character:pos.col

let to_lsp_range (r : range) : Range.t =
  Range.create ~start:(to_lsp_pos r.start) ~end_:(to_lsp_pos r.stop)

let located (span : LexingUtil.span) : Range.t  =
  to_lsp_range @@ of_lex_span span

let pp_range fmt range =
  Format.fprintf fmt "[%d:%d]-[%d:%d]"
    range.start.row range.start.col
    range.stop.row range.stop.col
