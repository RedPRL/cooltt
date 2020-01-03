module D = Domain
module StringMap = Map.Make (String)

type t = 
  {resolver : Symbol.t StringMap.t;
   globals : D.nf SymbolMap.t}

let init = 
  {resolver = StringMap.empty;
   globals = SymbolMap.empty}

let add_global ident tp el st = 
  let sym = Symbol.named ident in
  {resolver = StringMap.add ident sym st.resolver;
   globals = SymbolMap.add sym (D.Nf {term = el; tp}) st.globals}

let resolve_global ident st =
  StringMap.find_opt ident st.resolver

let get_global sym st =
  SymbolMap.find sym st.globals