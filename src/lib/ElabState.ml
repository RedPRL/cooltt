module D = Domain
module StringMap = Map.Make (String)

type t = 
  {resolver : Symbol.t StringMap.t;
   globals : D.nf SymbolMap.t}

let init = 
  {resolver = StringMap.empty;
   globals = SymbolMap.empty}

let add_global ident tp oel st = 
  let sym = Symbol.named_opt ident in
  let con = 
    match oel with
    | Some con -> con
    | None -> D.Cut {tp; cut = (D.Global sym, []), None}
  in
  sym, 
  {resolver = 
     begin
       match ident with 
       | Some ident -> StringMap.add ident sym st.resolver
       | None -> st.resolver
     end;
   globals = 
     SymbolMap.add sym (D.Nf {con; tp}) st.globals}

let resolve_global ident st =
  StringMap.find_opt ident st.resolver

let get_global sym st =
  SymbolMap.find sym st.globals