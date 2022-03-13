type +'a t

val empty : 'a t
val inherit_view : 'a t -> 'a t
val get_export : prefix:Namespace.path option -> 'a t -> 'a Namespace.t
val resolve : Ident.t -> 'a t -> 'a option

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

val include_ : shadowing:bool -> 'a Namespace.t -> 'a t -> ('a t, 'error) Namespace.result

val import : shadowing:bool -> 'a Namespace.t -> 'a t -> ('a t, 'error) Namespace.result
