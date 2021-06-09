open Basis

module D = Domain
module StringMap = Map.Make (String)

type t =
  { current_unit : string;
    code_units : CodeUnit.t StringMap.t;
  }

let init unit_name =
  { current_unit = unit_name;
    code_units = StringMap.singleton unit_name (CodeUnit.create unit_name) }

let get_current_unit st = StringMap.find st.current_unit st.code_units

let update_current_unit f st = { st with code_units = StringMap.update st.current_unit (Option.map f) st.code_units }

let set_current_unit code_unit st = { st with code_units = StringMap.add st.current_unit code_unit st.code_units }

let add_global ident tp ocon st =
  let code_unit = get_current_unit st in
  let (sym, code_unit') = CodeUnit.add_global ident tp ocon code_unit in
  (sym, set_current_unit code_unit' st)

let resolve_global ident st =
  let code_unit = get_current_unit st in
  CodeUnit.resolve_global ident code_unit

let get_global sym st =
  let unit_name = CodeUnit.origin sym in
  let code_unit = StringMap.find unit_name st.code_units in
  CodeUnit.get_global sym code_unit

let add_import path code_unit st =
  let st' = update_current_unit (CodeUnit.add_import path code_unit) st in
  { st' with code_units = StringMap.add (CodeUnit.name code_unit) code_unit st'.code_units }

let enter_unit unit_name st =
  print_string @@ "Entering Unit " ^ unit_name ^ "\n";
  { current_unit = unit_name;
    code_units = StringMap.add unit_name (CodeUnit.create unit_name) st.code_units }

let restore_unit unit_name st =
  { st with current_unit = unit_name }
