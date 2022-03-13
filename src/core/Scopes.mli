type +'a t

val init : 'a Scope.t -> 'a t

val transform_view :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  _ Namespace.pattern ->
  'a t -> ('a t, 'error) Namespace.result

val transform_export :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  _ Namespace.pattern ->
  'a t -> ('a t, 'error) Namespace.result

val export_view :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  _ Namespace.pattern ->
  'a t -> ('a t, 'error) Namespace.result

val add : shadowing:bool -> Ident.t -> 'a -> 'a t -> ('a t, 'error) Namespace.result
val import : shadowing:bool -> 'a Namespace.t -> 'a t -> ('a t, 'error) Namespace.result

val begin_ : 'a t -> 'a t
val end_ : shadowing:bool -> prefix:Namespace.path option -> 'a t -> ('a t, 'error) Namespace.result

val resolve : Ident.t -> 'a t -> 'a option
val export_top : 'a t -> 'a Namespace.t
