open CodeUnit

module IDMap = Map.Make (CodeUnitID)
module D = Domain

type t = { code_units : CodeUnit.t IDMap.t }

let init = { code_units = IDMap.empty }

let get_unit id st =
  IDMap.find id st.code_units

let update_unit id f st = { code_units = IDMap.update id (Option.map f) st.code_units }

let set_unit id code_unit st = { code_units = IDMap.add id code_unit st.code_units }

let add_global id ident tp ocon st =
  let code_unit = get_unit id st in
  let (sym, code_unit') = CodeUnit.add_global ident tp ocon code_unit in
  (sym, set_unit id code_unit' st)

let resolve_global id ident st =
  let code_unit = get_unit id st in
  CodeUnit.resolve_global ident code_unit

let get_global sym st =
  let unit_name = CodeUnit.origin sym in
  let code_unit = IDMap.find unit_name st.code_units in
  CodeUnit.get_global sym code_unit

let add_import id path code_unit st =
  update_unit id (CodeUnit.add_import path code_unit) st

let init_unit id st =
  { code_units = IDMap.add id (CodeUnit.create id) st.code_units }

let get_import path st =
  IDMap.find_opt path st.code_units
