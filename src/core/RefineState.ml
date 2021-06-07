open Basis

module D = Domain
module StringMap = Map.Make (String)

type t =
  { (** A namespace for the current module. *)
    current_scope : Namespace.t;
    (** The namespace of imports. These are kept separate so that creating interface files is simpler. *)
    imports : Namespace.t;
    (** The set of bindings currently in scope. This includes all bindings from the namespaces *)
    (* FIXME: Perhaps we ought to use an array here? We could get O(1) indexing. *)
    (* FIXME: We should make sure not to bloat the symbol table too much... *)
    globals : (D.tp * D.con option) SymbolMap.t
  }

let init =
  {current_scope = Namespace.empty;
   imports = Namespace.empty;
   globals = SymbolMap.empty}

let add_global (ident : Ident.t) tp ocon st =
  let sym = Symbol.named_opt @@ Ident.pp_name ident
  in
  sym,
  { st with current_scope = Namespace.add_symbol ident sym st.current_scope;
            globals = SymbolMap.add sym (tp, ocon) st.globals }

let add_flex_global tp st =
  let sym = Symbol.fresh () in
  sym,
  {st with
   globals = SymbolMap.add sym (tp, None) st.globals}

let resolve_global ident st =
  match Namespace.resolve_symbol ident st.current_scope with
  | Some sym -> Some sym
  | None -> Namespace.resolve_symbol ident st.imports

let get_global sym st =
  SymbolMap.find sym st.globals

let add_import path imp st =
  { st with imports = Namespace.add_namespace path imp.current_scope st.imports;
            globals = SymbolMap.union (fun key _ _ -> failwith @@ "Symbol Overlap: " ^ Symbol.show key) imp.globals st.globals }
