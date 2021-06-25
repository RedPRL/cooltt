open ContainersLabels
open Basis
open Bwd

module CodeUnitID =
struct
  type t = string option
  let compare = Option.compare String.compare
  let pp fmt id = Format.pp_print_string fmt (Option.value ~default:"<top-level>" id)
  let top_level : t = None
  let file s : t = Some s
end
type id = CodeUnitID.t

module Global =
struct
  type t =
    { origin : CodeUnitID.t;
      index : int;
      name : string option }
  [@@deriving show]

  let compare s1 s2 =
    Int.compare s1.index s2.index

  let equal s1 s2 =
    s1.index = s2.index

  let pp fmt sym =
    match sym.name with
    | Some nm ->
      Format.fprintf fmt "%a" Uuseg_string.pp_utf_8 nm
    | None ->
      Format.fprintf fmt "#%i" sym.index
end

module Domain = Domain.Make (Global)
module Syntax = Syntax.Make (Global)

module CodeUnit =
struct
  type t =
    { (* The name of the code unit.  *)
      id : id;
      (* The top-level namespace of this code unit. Import namespaces are stored separately. *)
      namespace : Global.t Namespace.t;
      (* The code unit names of all of this code unit's imports. *)
      imports : id bwd;
      (* The namespace of imports. *)
      import_namespace : Global.t Namespace.t;
      (* All the top-level bindings for this code unit. *)
      symbol_table :  (Domain.tp * Domain.con option) Vector.vector }

  let origin (sym : Global.t) = sym.origin

  let id code_unit = code_unit.id

  let imports code_unit = Bwd.to_list code_unit.imports

  let create id =
    { id = id;
      namespace = Namespace.empty;
      imports = Emp;
      import_namespace = Namespace.empty;
      symbol_table = Vector.create () }

  let add_global ident tp ocon code_unit =
    let index = Vector.length code_unit.symbol_table in
    let _ = Vector.push code_unit.symbol_table (tp, ocon) in
    let sym = { Global.origin = code_unit.id; index = index; name = Ident.to_string_opt ident } in
    let code_unit' = { code_unit with namespace = Namespace.add ident sym code_unit.namespace } in
    (sym, code_unit')

  let resolve_global ident code_unit =
    match Namespace.find ident code_unit.namespace with
    | Some sym -> Some sym
    | None -> Namespace.find ident code_unit.import_namespace

  let get_global (sym : Global.t) code_unit =
    Vector.get code_unit.symbol_table sym.index

  let add_import modifier import code_unit =
    { code_unit with import_namespace = Namespace.nest Global.pp modifier import.namespace code_unit.import_namespace;
                     imports = Snoc (code_unit.imports, code_unit.id) }
end
