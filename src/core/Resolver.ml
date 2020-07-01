open Basis
module Y = Yuujinchou

module PathOrd : Map.OrderedType with type t = Y.Pattern.path =
struct
  type t = Y.Pattern.path
  let compare = compare
end

module PathMap = Map.Make (PathOrd)

type env = Symbol.t PathMap.t
type pattern = unit Y.Pattern.pattern
type path = Y.Pattern.path

let empty = PathMap.empty
let singleton = PathMap.singleton

let remap : pattern -> env -> env =
  fun pattern ->
  let alg path sym env =
    match Result.get_ok @@ Y.Action.run_ pattern path with
    | `NoMatch -> env
    | `Matched results ->
      let alg (path, ()) env =
        match PathMap.find_opt path env with
        | None -> PathMap.add path sym env
        | Some sym' when sym <> sym' ->
          failwith "Inconsistent data assigned to the same path"
        | _ -> env
      in
      List.fold_right alg results env
  in
  fun env ->
  PathMap.fold alg env PathMap.empty

let import : ?pattern:pattern -> import:env -> env -> env =
  fun ?(pattern = Y.Pattern.any) ~import env ->
  let merge _ _ sym' = Some sym' in
  PathMap.union merge env @@
  remap pattern import

let find_opt = PathMap.find_opt
