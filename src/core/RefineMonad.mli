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

val add_global : shadowing:bool -> Ident.t -> D.tp -> D.con option -> Global.t m
val get_global : Global.t -> (D.tp * D.con option) m
val resolve : Ident.t -> [`Local of int | `Global of Global.t | `Unbound] m

val get_local_tp : int -> D.tp m
val get_local : int -> D.con m

val get_lib : Bantorra.Manager.library m
val with_unit : Bantorra.Manager.library -> id -> 'a m -> 'a m

val import : shadowing:bool -> _ Namespace.pattern -> id -> unit m
val loading_status : CodeUnitID.t -> [ `Loaded | `Loading | `Unloaded ] m

val view : shadowing:bool -> _ Namespace.pattern -> unit m
val export : shadowing:bool -> _ Namespace.pattern -> unit m
val repack : shadowing:bool -> _ Namespace.pattern -> unit m
val with_section : shadowing:bool -> prefix:Namespace.path option -> 'a m -> 'a m

val eval : S.t -> D.con m
val eval_tp : S.tp -> D.tp m

val quote_con : D.tp -> D.con -> S.t m
val quote_tp : D.tp -> S.tp m
val quote_cut : D.cut -> S.t m
val quote_cof : D.cof -> S.t m
val quote_dim : D.dim -> S.t m

val equate_tp : D.tp -> D.tp -> unit m
val equate : D.tp -> D.con -> D.con -> unit m

val with_pp : (Pp.env -> 'a m) -> 'a m

val expected_connective : RefineError.connective -> D.tp -> 'a m
val expected_field : D.sign -> S.t -> Ident.user -> 'a m
val field_names_mismatch : expected:Ident.user list -> actual:Ident.user list -> 'a m
