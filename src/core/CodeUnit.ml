open Basis
open Bwd

module Vector = CCVector

module D = Domain

type symbol = Symbol.t

type t =
  { (* The name of the code unit.  *)
    name : string;
    (* The top-level namespace of this code unit. Import namespaces are stored separately. *)
    namespace : symbol Namespace.t;
    (* The code unit names of all of this code unit's imports. *)
    imports : string bwd;
    (* The namespace of imports. *)
    import_namespace : symbol Namespace.t;
    (* All the top-level bindings for this code unit. *)
    symbol_table :  (D.tp * D.con option) Vector.vector }

let origin (sym : Symbol.t) = sym.origin

let name code_unit = code_unit.name

let imports code_unit = Bwd.to_list code_unit.imports

let create name =
  { name = name;
    namespace = Namespace.empty;
    imports = Emp;
    import_namespace = Namespace.empty;
    symbol_table = Vector.create () }

let add_global ident tp ocon code_unit =
  let index = Vector.length code_unit.symbol_table in
  let _ = Vector.push code_unit.symbol_table (tp, ocon) in
  let sym = { Symbol.origin = code_unit.name; index = index; name = Ident.to_string_opt ident } in
  let code_unit' = { code_unit with namespace = Namespace.add ident sym code_unit.namespace } in
  (sym, code_unit')

let resolve_global ident code_unit =
  match Namespace.find ident code_unit.namespace with
  | Some sym -> Some sym
  | None -> Namespace.find ident code_unit.import_namespace

let get_global (sym : Symbol.t) code_unit =
  Vector.get code_unit.symbol_table sym.index

let add_import path import code_unit =
  { code_unit with import_namespace = Namespace.nest path import.namespace code_unit.import_namespace;
                   imports = Snoc (code_unit.imports, code_unit.name) }
