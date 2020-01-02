module CS = ConcreteSyntax
module D = Domain

type t = 
  | Unbound_variable of CS.ident
  | ExpectedEqual of D.tp * D.t * D.t
  | ExpectedEqualTypes of D.tp * D.tp
  | InvalidTypeExpression of CS.t 
  | ExpectedPiType of D.tp
[@@deriving show]

exception ElabError of t