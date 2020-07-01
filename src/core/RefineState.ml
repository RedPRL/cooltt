open Basis

module D = Domain

type t =
  {resolver : Resolver.env;
   globals : (D.tp * D.con option) SymbolMap.t}

let init =
  {resolver = Resolver.empty;
   globals = SymbolMap.empty}

let add_global (ident : Ident.t) tp ocon st =
  let sym =
    Symbol.named_opt @@
    match ident with
    | `User id -> Some id
    | `Machine id -> Some id
    | `Anon -> None
  in
  sym,
  {resolver =
     begin
       match ident with
       | `User ident ->
         Resolver.import ~import:(Resolver.singleton [ident] sym) st.resolver
       | _ -> st.resolver
     end;
   globals = SymbolMap.add sym (tp, ocon) st.globals}

let add_flex_global tp st =
  let sym = Symbol.fresh () in
  sym,
  {st with
   globals = SymbolMap.add sym (tp, None) st.globals}

let resolve_global ident st =
  match ident with
  | `User id -> Resolver.resolve [id] st.resolver
  | _ -> None

let get_global sym st =
  SymbolMap.find sym st.globals

