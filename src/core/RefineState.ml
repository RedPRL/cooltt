open Basis

module D = Domain
module StringMap = Map.Make (String)

type namespace = {
    (** Used to resolve an identifier to a unique symbol in this namespace. *)
    symbols : Symbol.t StringMap.t;
    (** Namespaces may themselves contain other namespaces, so let's keep track of them. *)
    namespaces : namespace StringMap.t
  }

(* FIXME Implemnt adding of qualified names *)
let add_symbol (ident : Ident.t) sym ns =
  match ident with
  | `Unqual ident -> { ns with symbols = StringMap.add ident sym ns.symbols }
  | _           -> ns

let rec resolve_qualified modparts nm ns =
  match modparts with
  | []                  -> StringMap.find_opt nm ns.symbols
  | (modnm :: modparts) -> Option.bind (StringMap.find_opt modnm ns.namespaces) (resolve_qualified modparts nm)

(* FIXME Implemnt resolution of qualified names *)
let resolve_symbol (ident : Ident.t) ns =
  match ident with
  | `Unqual ident     -> StringMap.find_opt ident ns.symbols
  | `Qual (parts, nm) -> resolve_qualified parts nm ns
  | _                 -> None


type t =
  { (** A nested series of namespaces. The top-level namespace corresponds to the current one. *)
    resolver : namespace;
    (** The set of bindings currently in scope. This includes all bindings from the namespaces *)
    (* FIXME: Perhaps we ought to use an array here? We could get O(1) indexing. *)
    globals : (D.tp * D.con option) SymbolMap.t
  }

let init =
  {resolver = { symbols = StringMap.empty; namespaces = StringMap.empty };
   globals = SymbolMap.empty}

let add_global (ident : Ident.t) tp ocon st =
  let sym =
    Symbol.named_opt @@ Ident.pp_name ident
  in
  sym,
  {resolver = add_symbol ident sym st.resolver;
   globals = SymbolMap.add sym (tp, ocon) st.globals}

let add_flex_global tp st =
  let sym = Symbol.fresh () in
  sym,
  {st with
   globals = SymbolMap.add sym (tp, None) st.globals}

let resolve_global ident st = resolve_symbol ident st.resolver

let get_global sym st =
  SymbolMap.find sym st.globals

