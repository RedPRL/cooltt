type 'a t =
  { view : 'a Namespace.t
  ; export : 'a Namespace.t
  }

let empty = {view = Namespace.empty; export = Namespace.empty}
let get_export s = s.export
let find_view id s = Namespace.find id s.view

let (let*) = Result.bind
let (let+) x f = Result.map f x

let transform_view ~shadowing ~pp pattern s =
  let+ view = Namespace.transform ~shadowing ~pp pattern s.view in {s with view}
let transform_export ~shadowing ~pp pattern s =
  let+ export = Namespace.transform ~shadowing ~pp pattern s.export in {s with export}
let export_view ~shadowing ~pp pattern s =
  let* view = Namespace.transform ~shadowing ~pp pattern s.view in
  let+ export = Namespace.union ~shadowing s.export view in
  {view; export}
let add ~shadowing id sym s =
  let* view = Namespace.add ~shadowing id sym s.view in
  let+ export = Namespace.add ~shadowing id sym s.export in
  {view; export}
let incl ~shadowing ns s =
  let* view = Namespace.union ~shadowing s.view ns in
  let+ export = Namespace.union ~shadowing s.export ns in
  {view; export}
