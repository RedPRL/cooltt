type +'a t

val empty : 'a t
val get_export : 'a t -> 'a Namespace.t
val find_view : Ident.t -> 'a t -> 'a option

val transform_view :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  'b Namespace.pattern ->
  'a t -> ('a t, 'error) Namespace.result

val transform_export :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  'b Namespace.pattern ->
  'a t -> ('a t, 'error) Namespace.result

val export_view :
  shadowing:bool ->
  pp:(Format.formatter -> 'a -> unit) ->
  'b Namespace.pattern ->
  'a t -> ('a t, 'error) Namespace.result

val add : shadowing:bool -> Ident.t -> 'a -> 'a t -> ('a t, 'error) Namespace.result

val incl : shadowing:bool -> 'a Namespace.t -> 'a t -> ('a t, 'error) Namespace.result
