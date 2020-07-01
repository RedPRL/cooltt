open Basis
module SymMap = Map.Make (Symbol)
module NativeMap = Map.Make (Int)
module StringMap = Map.Make (String)

type symbol = Symbol.t
type native = int

type attr = [`Public | `Private]
type info = {symbol : symbol; attr : attr}

type env =
  {info_of_string : [`Native of native] StringMap.t;
   string_of_native : string NativeMap.t;
   info_of_native : info NativeMap.t;
   native_of_sym : native SymMap.t}

let empty =
  {info_of_string = StringMap.empty;
   string_of_native = NativeMap.empty;
   info_of_native = NativeMap.empty;
   native_of_sym = SymMap.empty}

let native_of_sym sym env : native option =
  SymMap.find_opt sym env.native_of_sym

let add_native ~attr (str : string option) (sym : symbol) (env : env) : env =
  let native, info_of_native, native_of_sym =
    match native_of_sym sym env with
    | Some native ->
      native, env.info_of_native, env.native_of_sym
    | None ->
      let native = NativeMap.cardinal env.info_of_native in
      native,
      NativeMap.add native {symbol = sym; attr = attr} env.info_of_native,
      SymMap.add sym native env.native_of_sym
  in

  let info_of_string, string_of_native =
    match str with
    | None -> env.info_of_string, env.string_of_native
    | Some str ->
      match StringMap.find_opt str env.info_of_string with
      | None ->
        StringMap.add str (`Native native) env.info_of_string,
        NativeMap.add native str env.string_of_native
      | Some (`Native old_native) when old_native = native ->
        env.info_of_string, env.string_of_native
      | Some (`Native old_native) ->
        StringMap.add str (`Native native) env.info_of_string,
        NativeMap.add native str @@ NativeMap.remove old_native env.string_of_native
  in

  {info_of_native; native_of_sym; info_of_string; string_of_native}

let native_of_symbol sym env =
  SymMap.find_opt sym env.native_of_sym

let symbol_of_native native env : symbol option =
  NativeMap.find_opt native env.info_of_native |> Option.map @@ fun info ->
  info.symbol

let resolve str env =
  match StringMap.find_opt str env.info_of_string with
  | Some (`Native native) ->
    symbol_of_native native env
  | None -> None



let unresolve sym env =
  match native_of_symbol sym env with
  | Some native ->
    NativeMap.find_opt native env.string_of_native
  | None -> None
