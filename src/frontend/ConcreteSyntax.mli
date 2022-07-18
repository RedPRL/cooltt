include module type of ConcreteSyntaxData

val show_con : con -> string
val pp_con : Format.formatter -> con -> unit

(* [HACK: June; 2022-07-14] See ConcreteSyntaxData *)
module J = Ezjsonm
module Y = Yojson.Safe

val yojson_of_ezjsonm : J.value -> Y.t
val ezjsonm_of_yojson : Y.t -> J.value

val con_of_yojson : Y.t -> con
val yojson_of_con : con -> Y.t
