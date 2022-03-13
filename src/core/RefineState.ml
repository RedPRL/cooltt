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

    (** global cofibration theory *)
    cof_thy : Cubical.CofThy.Disj.t;

    (** all known units (including the ones that are being processed), which keep the data associated with global symbols *)
    units : CodeUnit.t IDMap.t;
    (** all global cofibrations and namespaces exported by processed units (not including the ones in proccessing) *)
    exports : (Global.t Namespace.t * Cubical.CofThy.Disj.t) IDMap.t;
  }

let init lib =
  let unit_id = CodeUnitID.top_level in
  { lib;
    unit_id;
    scopes = Scopes.init Scope.empty;
    cof_thy = Cubical.CofThy.Disj.empty;
    units = IDMap.singleton unit_id (CodeUnit.create unit_id);
    exports = IDMap.empty;
  }

(* lib *)
let get_lib st = st.lib

(* scopes *)
let modify_scopes f st = { st with scopes = f st.scopes }
let begin_section st = modify_scopes Scopes.begin_ st

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
let end_section ~shadowing ~prefix = modify_scopes (Scopes.end_ ~shadowing ~prefix)

(* unit *)
let get_unit id st = IDMap.find id st.units

let resolve_global id st = Scopes.resolve id st.scopes
let add_global ident tp ocon st =
  let open Result in
  let unit = get_unit st.unit_id st in
  let (sym, unit) = CodeUnit.add_global ident tp ocon unit in
  let cof_thy =
    match tp with
    | D.TpPrf phi -> Cubical.CofThy.Disj.assume st.cof_thy [phi]
    | _ -> st.cof_thy
  in
  let+ scopes = Scopes.add ~shadowing:true ident sym st.scopes in
  sym, { st with cof_thy; scopes; units = IDMap.add st.unit_id unit st.units }

let get_global sym st =
  CodeUnit.get_global sym @@ get_unit (CodeUnit.origin sym) st

let get_global_cof_thy st = st.cof_thy

let begin_unit lib unit_id st =
  { lib; unit_id;
    scopes = Scopes.init Scope.empty;
    cof_thy = Cubical.CofThy.Disj.empty;
    units = IDMap.add unit_id (CodeUnit.create unit_id) st.units;
    exports = st.exports;
  }

let end_unit ~parent ~child =
  { lib = parent.lib;
    unit_id = parent.unit_id;
    scopes = parent.scopes;
    cof_thy = parent.cof_thy;
    units = child.units;
    exports = IDMap.add child.unit_id (Scopes.export_top child.scopes, child.cof_thy) child.exports;
  }

let import ~shadowing pat unit_id st =
  let open Result in
  let ns, cof_thy = IDMap.find unit_id st.exports in
  let* ns = Namespace.transform ~shadowing ~pp:Global.pp pat ns in
  let cof_thy = Cubical.CofThy.Disj.meet2 st.cof_thy cof_thy in
  let+ scopes = Scopes.import ~shadowing ns st.scopes in
  { st with scopes; cof_thy }

let loading_status unit_id st =
  if IDMap.mem unit_id st.exports then
    `Loaded
  else if IDMap.mem unit_id st.exports then
    `Loading
  else
    `Unloaded
