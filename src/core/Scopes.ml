open Basis

type ('a, 'depth) t = ('a Scope.t, 'depth SizedList.succ) SizedList.t

module SL = SizedList

let empty = SL.Cons (Scope.empty, SL.Nil)

let push = SL.cons

let pop = SL.uncons

let map_current ~f ss =
  let (s, ss) = pop ss in
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
  map_current ss ~f:(Scope.incl ~shadowing (Scope.get_export s))



(*
section begin
   // blah blah

   view pattern // apply the pattern to the current view. "open m" is simply "view [m -> ]". errors on name conflicts.
   !view pattern // no errors on name conflicts.

   def .... // this is added to the current view AND the export list

   export pattern // apply the pattern to the current view, and then add those to the exported bindings. errors on name conflicts.
   !export pattern // no errors on name conflicts.

   reexport pattern // apply the pattern to what's being exported; errors on name conflicts
   !reexport pattern // no errors on name conflicts.

end [pattern] <-- this is effectively "reexport pattern" at the end.
*)
