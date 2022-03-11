open Basis
open Bwd

type 'a t = 'a Scope.t bwd

let init s = Snoc (Emp, s)

let push s ss = Snoc (ss, s)

let pop =
  function
  | Emp -> invalid_arg "Scopes.pop"
  | Snoc (ss, s) -> s, ss

let map_current ~f ss =
  let s, ss = pop ss in
  Result.bind (f s) @@ fun s ->
  Result.ok (push s ss)

let transform_view ~shadowing ~pp pattern ss =
  map_current ss ~f:(Scope.transform_view ~shadowing ~pp pattern)
let transform_export ~shadowing ~pp pattern ss =
  map_current ss ~f:(Scope.transform_export ~shadowing ~pp pattern)
let export_view ~shadowing ~pp pattern ss =
  map_current ss ~f:(Scope.export_view ~shadowing ~pp pattern)
let add ~shadowing id sym ss =
  map_current ss ~f:(Scope.add ~shadowing id sym)
let fold ~shadowing ss =
  let (s, ss) = pop ss in
  map_current ss ~f:(Scope.include_ ~shadowing (Scope.get_export s))
let import ~shadowing ns ss =
  map_current ss ~f:(Scope.import ~shadowing ns)

let rec resolve id =
  function
  | Emp -> None
  | Snoc (ss, s) ->
    match Scope.find_view id s with
    | Some x -> Some x
    | None -> resolve id ss
let export_top =
  function
  | Snoc (Emp, s) -> Scope.get_export s
  | _ -> invalid_arg "Scopes.export_top"
