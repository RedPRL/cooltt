open Basis

module S = Syntax
module StringMap = Map.Make (String)

type t =
  {resolver : Symbol.t StringMap.t;
   globals : Decl.t SymbolMap.t}

let init =
  {resolver = StringMap.empty;
   globals = SymbolMap.empty}

let add_global (ident : Ident.t) decl st =
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
       | `User ident -> StringMap.add ident sym st.resolver
       | _ -> st.resolver
     end;
   globals = SymbolMap.add sym decl st.globals}

let resolve_global ident st =
  match ident with
  | `User id -> StringMap.find_opt id st.resolver
  | _ -> None

let get_global sym st =
  SymbolMap.find sym st.globals

