open CoolBasis

module D = Domain
module StringMap = Map.Make (String)

type t =
  {resolver : Symbol.t StringMap.t;
   flexity : [`Flex | `Rigid] SymbolMap.t;
   globals : (D.tp * D.con option) SymbolMap.t}

let init =
  {resolver = StringMap.empty;
   flexity = SymbolMap.empty;
   globals = SymbolMap.empty}

let add_global ident tp ocon st =
  let sym = Symbol.named_opt ident in
  sym,
  {resolver =
     begin
       match ident with
       | Some ident -> StringMap.add ident sym st.resolver
       | None -> st.resolver
     end;
   flexity = SymbolMap.add sym `Rigid st.flexity;
   globals = SymbolMap.add sym (tp, ocon) st.globals}

let add_flex_global tp st =
  let sym = Symbol.fresh () in
  sym,
  {st with
   flexity = SymbolMap.add sym `Flex st.flexity;
   globals = SymbolMap.add sym (tp, None) st.globals}

let resolve_global ident st =
  StringMap.find_opt ident st.resolver

let get_global sym st =
  SymbolMap.find sym st.globals

let get_flexity sym st =
  SymbolMap.find sym st.flexity
