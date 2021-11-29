open Basis

include SegmentTree.POSITION

val of_lex_pos : LexingUtil.position -> t
val of_lsp_pos : Lsp.Types.Position.t -> t

val to_lsp_pos : t -> Lsp.Types.Position.t

val of_lex_span : LexingUtil.span -> range
val of_lsp_range : Lsp.Types.Range.t -> range

val to_lsp_range : range -> Lsp.Types.Range.t

val located : LexingUtil.span -> Lsp.Types.Range.t
