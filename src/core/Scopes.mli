type t

val init : Scope.t -> t

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
val import : shadowing:bool -> Namespace.t -> t -> (t, 'error) Namespace.result

val begin_ : t -> t
val end_ : shadowing:bool -> prefix:Namespace.path option -> t -> (t, 'error) Namespace.result

val resolve : Ident.t -> t -> CodeUnit.Global.t option
val export_top : t -> Namespace.t
