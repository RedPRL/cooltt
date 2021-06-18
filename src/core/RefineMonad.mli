open CodeUnit
module D = Domain
module S = Syntax

open Basis
open Bwd

include module type of Monads.RefineM

val push_problem : string -> 'a m -> 'a m
val problem : string bwd m

val refine_err : RefineError.t -> 'a m

val update_span : LexingUtil.span option -> 'a m -> 'a m
val abstract : Ident.t -> D.tp -> (D.con -> 'a m) -> 'a m

val add_global : Ident.t -> Definition.t -> Global.t m

val resolve : Ident.t -> [`Local of int | `Global of Global.t | `Unbound] m
val get_global : Global.t -> Definition.t m
val get_local_tp : int -> D.tp m
val get_global_tp : Global.t -> D.tp m
val get_local : int -> D.con m

val with_code_unit : string -> (unit -> 'a m) -> 'a m
val get_current_unit : CodeUnit.t m

val add_import : string list -> CodeUnit.t -> unit m
val get_import : string -> (CodeUnit.t option) m

val quote_con : D.tp -> D.con -> S.t m
val quote_tp : D.tp -> S.tp m
val quote_cut : D.cut -> S.t m
val quote_cof : D.cof -> S.t m
val quote_dim : D.dim -> S.t m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.con -> D.con -> unit m

val with_pp : (Pp.env -> 'a m) -> 'a m

val expected_connective : RefineError.connective -> D.tp -> 'a m
