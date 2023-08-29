type t

val empty : t
val inherit_view : t -> t
val get_export : prefix:Namespace.path option -> t -> Namespace.t
val resolve : Ident.t -> t -> CodeUnit.Global.t option

val transform_view :
  shadowing:bool ->
  pp:(Format.formatter -> CodeUnit.Global.t -> unit) ->
  Namespace.pattern ->
  t -> (t, 'error) Namespace.result

val transform_export :
  shadowing:bool ->
  pp:(Format.formatter -> CodeUnit.Global.t -> unit) ->
  Namespace.pattern ->
  t -> (t, 'error) Namespace.result

val export_view :
  shadowing:bool ->
  pp:(Format.formatter -> CodeUnit.Global.t -> unit) ->
  Namespace.pattern ->
  t -> (t, 'error) Namespace.result

val add : shadowing:bool -> Ident.t -> CodeUnit.Global.t -> t -> (t, 'error) Namespace.result

val include_ : shadowing:bool -> Namespace.t -> t -> (t, 'error) Namespace.result

val import : shadowing:bool -> Namespace.t -> t -> (t, 'error) Namespace.result
