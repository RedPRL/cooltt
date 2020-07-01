open Basis
module Y = Yuujinchou

module PathOrd : Map.OrderedType with type t = Y.Pattern.path =
struct
  type t = Y.Pattern.path
  let compare = compare
end

module SymMap = Map.Make (Symbol)
module PathMap = Map.Make (PathOrd)
module PathSet = Set.Make (PathOrd)

module Attr : sig
  type t
  val default : t
  val join : t -> t -> t
  val meet : t -> t -> t
end =
struct
  type t = unit
  let default = ()
  let join _ _ = ()
  let meet _ _ = ()
end

type attr = Attr.t
type pattern = attr Y.Pattern.pattern
type path = Y.Pattern.path
type symbol = Symbol.t

exception InconsistentMapping of path * symbol * symbol


module Env :
sig
  type env
  val empty : env
  val singleton : path -> symbol -> attr -> env
  val merge : env -> env -> env

  val resolve : path -> env -> (symbol * attr) option
  val unresolve : symbol -> env -> PathSet.t
  val fold : (path -> symbol * attr -> 'b -> 'b) -> env -> 'b -> 'b
end =
struct
  type env =
    {symbols : (symbol * attr) PathMap.t;
     paths : PathSet.t SymMap.t}

  let empty =
    {symbols = PathMap.empty;
     paths = SymMap.empty}

  let singleton path sym attr =
    {symbols = PathMap.singleton path (sym, attr);
     paths = SymMap.singleton sym @@ PathSet.singleton path}

  let merge env env' =
    {symbols = PathMap.union (fun _ _ -> Option.some) env.symbols env'.symbols;
     paths = SymMap.union (fun _ ps ps' -> Option.some @@ PathSet.union ps ps') env.paths env'.paths}

  let resolve path env =
    PathMap.find_opt path env.symbols

  let unresolve sym env =
    Option.value ~default:PathSet.empty @@
    SymMap.find_opt sym env.paths

  let fold alg env = PathMap.fold alg env.symbols
end

include Env

let remap_symbol : pattern -> path -> symbol * attr -> env -> env =
  fun pattern path (sym, attr) env ->
    match Result.get_ok @@ Y.Action.run ~default:Attr.default ~join:Attr.join ~meet:Attr.meet pattern path with
    | `NoMatch -> env
    | `Matched results ->
      let alg (path, attr') env =
        match resolve path env with
        | None -> merge env @@ singleton path sym @@ Attr.join attr attr'
        | Some (sym', _) when sym <> sym' ->
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

