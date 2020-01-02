module CS = ConcreteSyntax
module D = Domain

type error = 
  | Unbound_variable of CS.ident
  | ExpectedEqual of D.tp * D.t * D.t
  | ExpectedEqualTypes of D.tp * D.tp
  | InvalidTypeExpression of CS.t 
  | ExpectedPiType of D.tp

exception ElabError of error