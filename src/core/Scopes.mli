open Basis

type (+'a, 'depth) t

val empty : ('a, SizedList.zero) t

val push : 'a Scope.t -> ('a, 'depth) t -> ('a, 'depth SizedList.succ) t

val transform_view :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  'b Namespace.pattern ->
  ('a, 'depth) t -> (('a, 'depth) t, 'error) Namespace.result

val transform_export :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  'b Namespace.pattern ->
  ('a, 'depth) t -> (('a, 'depth) t, 'error) Namespace.result

val export_view :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  'b Namespace.pattern ->
  ('a, 'depth) t -> (('a, 'depth) t, 'error) Namespace.result

val add : shadowing:bool -> Ident.t -> 'a -> ('a, 'depth) t -> (('a, 'depth) t, 'error) Namespace.result

val fold : shadowing:bool -> ('a, 'depth SizedList.succ) t -> (('a, 'depth) t, 'error) Namespace.result
