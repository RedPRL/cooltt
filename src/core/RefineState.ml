open ContainersLabels
open CodeUnit

module IDMap = Map.Make (CodeUnitID)
module D = Domain

type t =
  {
    (** current library manager *)
    lib : Bantorra.Manager.library;
    (** current unit ID *)
    unit_id : CodeUnitID.t;
    (** current nested scopes *)
    scopes : Global.t Scopes.t;

    (** all known units (including the ones that are being processed), which keep the data associated with global symbols *)
    units : CodeUnit.t IDMap.t;
    (** all namespaces exported by processed units (not including the ones in proccessing) *)
    exports : Global.t Namespace.t IDMap.t;
  }

let init lib =
  let unit_id = CodeUnitID.top_level in
  { lib;
    unit_id;
    scopes = Scopes.init Scope.empty;
    units = IDMap.singleton unit_id (CodeUnit.create unit_id);
    exports = IDMap.empty }

(* lib *)
let get_lib st = st.lib

(* unit id *)
let get_unit_id st = st.unit_id
let set_unit_id unit_id st = {st with unit_id}

(* scopes *)
let modify_scopes f st = { st with scopes = f st.scopes }
let push_scope s = modify_scopes (Scopes.push s)
let modify_scopes f st =
  let open Result in
  let+ scopes = f st.scopes in
  { st with scopes }
let transform_view ~shadowing pattern =
  modify_scopes (Scopes.transform_view ~shadowing ~pp:Global.pp pattern)
let transform_export ~shadowing pattern =
  modify_scopes (Scopes.transform_export ~shadowing ~pp:Global.pp pattern)
let export_view ~shadowing pattern =
  modify_scopes (Scopes.export_view ~shadowing ~pp:Global.pp pattern)
let import ~shadowing ns = modify_scopes (Scopes.import ~shadowing ns)
let fold ~shadowing = modify_scopes (Scopes.fold ~shadowing)
let resolve_global id st = Scopes.resolve id st.scopes

(* unit *)
let get_unit id st = IDMap.find id st.units

let add_global ident tp ocon st =
  let open Result in
  let unit = get_unit st.unit_id st in
  let (sym, unit) = CodeUnit.add_global ident tp ocon unit in
  let+ scopes = Scopes.add ~shadowing:true ident sym st.scopes in
  sym, { st with scopes; units = IDMap.add st.unit_id unit st.units }

let get_global sym st =
  CodeUnit.get_global sym @@ get_unit (CodeUnit.origin sym) st

let get_export unit_id st =
  IDMap.find unit_id st.exports

let begin_unit lib unit_id st =
  { lib; unit_id;
    scopes = Scopes.init Scope.empty;
    units = IDMap.add unit_id (CodeUnit.create unit_id) st.units;
    exports = st.exports }

let end_unit ~parent ~child =
  { lib = parent.lib;
    unit_id = parent.unit_id;
    scopes = parent.scopes;
    units = child.units;
    exports = IDMap.add child.unit_id (Scopes.export_top child.scopes) child.exports }

let loading_status unit_id st =
  if IDMap.mem unit_id st.exports then
    `Loaded
  else if IDMap.mem unit_id st.exports then
    `Loading
  else
    `Unloaded
