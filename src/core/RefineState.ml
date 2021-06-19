open CodeUnit

module IDMap = Map.Make (CodeUnitID)
module D = Domain

type t =
  { current_unit : id;
    code_units : CodeUnit.t IDMap.t;
  }

let init unit_name =
  { current_unit = unit_name;
    code_units = IDMap.singleton unit_name (CodeUnit.create unit_name) }

let get_current_unit st = IDMap.find st.current_unit st.code_units

let update_current_unit f st = { st with code_units = IDMap.update st.current_unit (Option.map f) st.code_units }

let set_current_unit code_unit st = { st with code_units = IDMap.add st.current_unit code_unit st.code_units }

let add_global ident tp ocon st =
  let code_unit = get_current_unit st in
  let (sym, code_unit') = CodeUnit.add_global ident tp ocon code_unit in
  (sym, set_current_unit code_unit' st)

let resolve_global ident st =
  let code_unit = get_current_unit st in
  CodeUnit.resolve_global ident code_unit

let get_global sym st =
  let unit_name = CodeUnit.origin sym in
  let code_unit = IDMap.find unit_name st.code_units in
  CodeUnit.get_global sym code_unit

let add_import path code_unit st =
  let st' = update_current_unit (CodeUnit.add_import path code_unit) st in
  { st' with code_units = IDMap.add (CodeUnit.id code_unit) code_unit st'.code_units }

let get_import path st =
  IDMap.find_opt path st.code_units

let enter_unit unit_name st =
  { current_unit = unit_name;
    code_units = IDMap.add unit_name (CodeUnit.create unit_name) st.code_units }

let restore_unit unit_name st =
  { st with current_unit = unit_name }
