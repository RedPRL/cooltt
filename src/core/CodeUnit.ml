open Basis

module Vector = CCVector

module D = Domain

type symbol = Symbol.t

type t =
  { name : string;
    namespace : symbol Namespace.t;
    imports : symbol Namespace.t;
    symbol_table :  (D.tp * D.con option) Vector.vector }

let origin (sym : Symbol.t) = sym.origin

let name code_unit = code_unit.name

let create name =
  { name = name;
    namespace = Namespace.empty;
    imports = Namespace.empty;
    symbol_table = Vector.create () }

let add_global ident tp ocon code_unit =
  let index = Vector.length code_unit.symbol_table in
  let _ = Vector.push code_unit.symbol_table (tp, ocon) in
  let sym = { Symbol.origin = code_unit.name; index = index; name = Ident.pp_name ident } in
  let code_unit' = { code_unit with namespace = Namespace.add ident sym code_unit.namespace } in
  (sym, code_unit')

let resolve_global ident code_unit =
  match Namespace.find ident code_unit.namespace with
  | Some sym -> Some sym
  | None -> Namespace.find ident code_unit.imports

let get_global (sym : Symbol.t) code_unit =
  Vector.get code_unit.symbol_table sym.index

let add_import path import code_unit =
  { code_unit with imports = Namespace.nest path import.namespace code_unit.imports }
