module D = Domain
module StringMap = Map.Make (String)

type t = 
  {resolver : Symbol.t StringMap.t;
   flexity : [`Flex | `Rigid] SymbolMap.t;
   globals : D.nf SymbolMap.t}

let init = 
  {resolver = StringMap.empty;
   flexity = SymbolMap.empty;
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
   flexity = SymbolMap.add sym `Rigid st.flexity;
   globals = SymbolMap.add sym (D.Nf {con; tp}) st.globals}

let add_flex_global tp st =
  let sym = Symbol.fresh () in
  let con = D.Cut {tp; cut = (D.Global sym, []), None} in
  sym, 
  {st with 
   flexity = SymbolMap.add sym `Flex st.flexity;
   globals = SymbolMap.add sym (D.Nf {con; tp}) st.globals}

let resolve_global ident st =
  StringMap.find_opt ident st.resolver

let get_global sym st =
  SymbolMap.find sym st.globals

let get_flexity sym st =
  SymbolMap.find sym st.flexity