open CodeUnit

module IDMap = Map.Make (CodeUnitID)
module D = Domain

type t = { code_units : CodeUnit.t IDMap.t;
           (** The binding namespace for each code unit. *)
           namespaces : (Global.t Namespace.t) IDMap.t;
           (** The import namespace for each code unit. *)
           import_namespaces : (Global.t Namespace.t) IDMap.t }

let init =
  { code_units = IDMap.empty;
    namespaces = IDMap.empty;
    import_namespaces = IDMap.empty }

let get_unit id st =
  IDMap.find id st.code_units

let get_namespace id st =
  IDMap.find id st.namespaces

let get_imports id st =
  IDMap.find id st.import_namespaces

let update_unit id f st = { st with code_units = IDMap.update id (Option.map f) st.code_units }

let update_namespace id f st = { st with namespaces = IDMap.update id (Option.map f) st.namespaces }

let update_imports id f st = { st with import_namespaces = IDMap.update id (Option.map f) st.import_namespaces }

let add_global id ident tp ocon st =
  let code_unit = get_unit id st in
  let namespace = get_namespace id st in
  let (sym, code_unit') = CodeUnit.add_global ident tp ocon code_unit in
  let namespace' = Namespace.add ident sym namespace in
  let st' =
    { st with code_units = IDMap.add id code_unit' st.code_units;
              namespaces = IDMap.add id namespace' st.namespaces }
  in
  (sym, st')

let resolve_global id ident st =
  match Namespace.find ident (get_namespace id st) with
  | Some sym -> Some sym
  | None -> Namespace.find ident (get_imports id st)

let get_global sym st =
  let unit_name = CodeUnit.origin sym in
  let code_unit = get_unit unit_name st in
  CodeUnit.get_global sym code_unit

let add_import id modifier import_id st =
  let import_ns = get_namespace import_id st in
  update_imports id (Namespace.nest Global.pp modifier import_ns) st

let init_unit id st =
  { code_units = IDMap.add id (CodeUnit.create id) st.code_units;
    namespaces = IDMap.add id Namespace.empty st.namespaces;
    import_namespaces = IDMap.add id Namespace.empty st.import_namespaces }

let get_import path st =
  IDMap.find_opt path st.code_units

let is_imported path st =
  IDMap.mem path st.code_units
