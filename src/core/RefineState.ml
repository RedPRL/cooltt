open Basis

module D = Domain
module StringMap = Map.Make (String)
module SymbolTable = SymbolTable.Make (Symbol)

type t =
  { current_unit : string;
    code_units : CodeUnit.t StringMap.t;
    globals : (D.tp * D.con option) SymbolTable.t
  }

let init unit_name =
  { current_unit = unit_name;
    code_units = StringMap.singleton unit_name (CodeUnit.create 0);
    globals = SymbolTable.empty ()}

(* Helpers for getting/modifying the current code unit *)

let get_current_unit st = StringMap.find st.current_unit st.code_units

let update_current_unit f st =
  { st with code_units = StringMap.update st.current_unit (Option.map f) st.code_units }

(* Conversion between fuly qualified names and symbols *)

let sym_to_fqn (sym : Symbol.t) st =
  let cunit = get_current_unit st in
  let index = sym.gen - cunit.offset in
  { CodeUnit.code_unit = st.current_unit; index = index }

(* Symbol Management *)

let add_global (ident : Ident.t) tp ocon st =
  let sym = SymbolTable.named_opt (Ident.pp_name ident) (tp, ocon) st.globals in
  let fqn = sym_to_fqn sym st in
  (sym, update_current_unit (CodeUnit.add_global ident fqn) st)

let resolve_global ident st =
  let cunit = get_current_unit st in
  let ofqn = CodeUnit.resolve_global ident cunit in
  Option.map (fun (fqn : CodeUnit.fqn) -> {  Symbol.gen = fqn.index + cunit.offset; Symbol.name = Ident.pp_name ident }) ofqn

let get_global sym st =
  SymbolTable.find sym st.globals

(* FIXME: Actually implement this! *)
let add_import path imp st = st
  (* { st with code_units = StringMap.update st.current_unit (Namespace.add_namespace __) st.code_units;
   *           globals = __
   *             (\* SymbolMap.union (fun key _ _ -> failwith @@ "Symbol Overlap: " ^ Symbol.show key) imp.globals st.globals *\)
   * } *)
