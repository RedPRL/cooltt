open Basis
module Y = Yuujinchou

module PathOrd : Map.OrderedType with type t = Y.Pattern.path =
struct
  type t = Y.Pattern.path
  let compare = compare
end

module SymMap = Map.Make (Symbol)
module PathMap = Map.Make (PathOrd)

type pattern = unit Y.Pattern.pattern
type path = Y.Pattern.path
type symbol = Symbol.t

exception InconsistentMapping of path * symbol * symbol


module Env :
sig
  type env
  val empty : env
  val singleton : path -> symbol -> env
  val merge : env -> env -> env

  val resolve : path -> env -> symbol option
  val unresolve : symbol -> env -> path list
  val fold : (path -> symbol -> 'b -> 'b) -> env -> 'b -> 'b
end =
struct
  type env =
    {symbols : symbol PathMap.t;
     paths : path list SymMap.t}

  let empty =
    {symbols = PathMap.empty;
     paths = SymMap.empty}

  let singleton path sym =
    {symbols = PathMap.singleton path sym;
     paths = SymMap.singleton sym [path]}

  let merge env env' =
    {symbols = PathMap.union (fun _ _ -> Option.some) env.symbols env'.symbols;
     paths = SymMap.union (fun _ ps ps' -> Option.some @@ ps @ ps') env.paths env'.paths}

  let resolve path env =
    PathMap.find_opt path env.symbols

  let unresolve sym env =
    Option.value ~default:[] @@
    SymMap.find_opt sym env.paths

  let fold alg env = PathMap.fold alg env.symbols
end

include Env

let remap_symbol : pattern -> path -> symbol -> env -> env =
  fun pattern path sym env ->
    match Result.get_ok @@ Y.Action.run_ pattern path with
    | `NoMatch -> env
    | `Matched results ->
      let alg (path, ()) env =
        match resolve path env with
        | None -> merge env @@ singleton path sym
        | Some sym' when sym <> sym' ->
          raise @@ InconsistentMapping (path, sym, sym')
        | _ -> env
      in
      List.fold_right alg results env

let remap : pattern -> env -> env =
  fun pattern env ->
  fold (remap_symbol pattern) env empty

let import : ?pattern:pattern -> import:env -> env -> env =
  fun ?(pattern = Y.Pattern.any) ~import env ->
  merge env @@ remap pattern import

