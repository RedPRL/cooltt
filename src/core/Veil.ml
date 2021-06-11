open Basis 

module Global = CodeUnit.Global
module SymbolMap = SymbolMap.Make (Global)

type policy = [`Translucent | `Transparent]
[@@deriving show]

type t = {default : policy; custom : policy SymbolMap.t}
[@@deriving show]

let policy : Global.t -> t -> policy =
  fun sym veil ->
  match SymbolMap.find_opt sym veil.custom with
  | Some p -> p
  | None -> veil.default

let unfold syms veil =
  {veil with
   custom =
     List.fold_left (fun m sym -> SymbolMap.add sym `Transparent m) veil.custom syms}

let const : policy -> t =
  fun p ->
  {default = p; custom = SymbolMap.empty}
